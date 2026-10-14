-- Prove2me | Definitions.Def_IntMul_HvdH_ConvR
-- name    : IntMul_HvdH_ConvR
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T02:05:01.515802+00:00
-- url     : https://prove2.me/theorems/ad497405-7fa4-454d-8c9f-cf77557bafd9
-- title:
--   Convolution over C[y]/(y^r+1) via synthetic FFTs (Harvey–van der Hoeven §3.1)
-- statement:
--   Definitions for Harvey–van der Hoeven §3.1 (Propositions 3.3 and 3.4). Let $R=\mathbb C[y]/(y^r+1)$. An element of $\bigotimes_{i<d}R^{t_i}$ with $t_i=2^{e_i}$ is stored as an array $x:\mathbb N^{d+1}\to\mathbb C$. The first $d$ coordinates index the $R$-axes and the last coordinate is the exponent of $y$. Fixed-point arrays $U$ with entries in $\mathbb Z[i]$ stand for $2^{-p}U$.
--
--   * `rSlice`, `rComp` and `rTensor` apply one-dimensional maps on $R$-vectors along each $R$-axis.
--   * `synGd r e` is the multidimensional normalised synthetic transform $\mathcal G_{t_1,\dots,t_d}$, built from `synG` (`IntMul_HvdH_SynFFT`). `synGdInv` is $\mathcal G^*$, the same transform composed with index negation (`negIdx`).
--   * `synGad` and `synGadInv` are their fixed-point versions.
--   * `negaCoeff r a b c` is the coefficient of $y^c$ in $ab\in R$.
--   * `mulPt r u v` is the exact normalised pointwise product $u_jv_j/r$.
--   * `mulPtZ` computes the fixed-point pointwise product by Kronecker substitution (`mulR`, Lemma 2.5).
--   * `scaleZ p k` is Lemma 2.2 for $c=2^k$. It multiplies by $2^k$ and pulls the result back into the disc of radius $2^p$ if it leaves it.
--   * `convRa p r e U V` is the algorithm of Proposition 3.4,
--   $$\tilde{\mathcal M}_R(U,V)=\mathrm{scale}_{T/r}\bigl(\tilde{\mathcal G}^*(\tilde A(\tilde{\mathcal G}U,\tilde{\mathcal G}V))\bigr),\qquad T/r=2^{\sum_i e_i}.$$
--   * `convR r e u v` is the exact normalised convolution $\mathcal M_R(u,v)=\tfrac1T\,u*v$, with $T=r\prod_i t_i$. It is cyclic in each $R$-axis and negacyclic in $y$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §3.1

import Definitions.Def_IntMul_HvdH_SynFFT
import Definitions.Def_IntMul_HvdH_KronMul
import Definitions.Def_IntMul_HvdH_SApprox

/-! Convolution over `R = ℂ[y]/(y^r + 1)` via synthetic FFTs (Harvey–van der Hoeven Prop. 3.3–3.4).
An element of `⊗_{i<d} R^{t_i}` is stored as an array `x : (Fin (d+1) → ℕ) → β`, where axis
`i.castSucc` (for `i : Fin d`) is the `i`-th `R`-axis and the last axis `Fin.last d` holds the
coefficient of `y^c`. Fixed-point arrays `U : … → ℤ × ℤ` stand for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- Apply a map on `R`-vectors (arrays `ℕ × ℕ → β` of (index, coefficient)) along `R`-axis `i`. -/
def rSlice {β : Type*} {d : ℕ} (i : Fin d) (A : ((ℕ × ℕ) → β) → ((ℕ × ℕ) → β))
    (x : (Fin (d + 1) → ℕ) → β) : (Fin (d + 1) → ℕ) → β :=
  fun j => A (fun kc => x (Function.update (Function.update j i.castSucc kc.1) (Fin.last d) kc.2))
    (j i.castSucc, j (Fin.last d))

/-- Apply the maps `A i` along the `R`-axes listed in `l`, first axis first. -/
def rComp {β : Type*} {d : ℕ} (A : Fin d → ((ℕ × ℕ) → β) → ((ℕ × ℕ) → β)) :
    List (Fin d) → ((Fin (d + 1) → ℕ) → β) → ((Fin (d + 1) → ℕ) → β)
  | [] => id
  | i :: l => rComp A l ∘ rSlice i (A i)

/-- The tensor product `⊗ᵢ Aᵢ` over all `R`-axes. -/
def rTensor {β : Type*} {d : ℕ} (A : Fin d → ((ℕ × ℕ) → β) → ((ℕ × ℕ) → β)) :
    ((Fin (d + 1) → ℕ) → β) → ((Fin (d + 1) → ℕ) → β) :=
  rComp A (List.finRange d)

/-- Index negation `k ↦ -k mod 2^e` on an `R`-vector of length `2^e`; `G*_t = negIdx ∘ G_t`. -/
def negIdx {β : Type*} (e : ℕ) (u : (ℕ × ℕ) → β) (kc : ℕ × ℕ) : β :=
  u ((2 ^ e - kc.1 % 2 ^ e) % 2 ^ e, kc.2)

/-- The multidimensional normalised synthetic transform `G_{t_1,…,t_d}` with `t_i = 2^{e_i}`. -/
noncomputable def synGd {d : ℕ} (r : ℕ) (e : Fin d → ℕ) :
    ((Fin (d + 1) → ℕ) → ℂ) → ((Fin (d + 1) → ℕ) → ℂ) :=
  rTensor fun i => synG r (e i)

/-- Its inverse-direction counterpart `G*_{t_1,…,t_d}` (conjugate roots). -/
noncomputable def synGdInv {d : ℕ} (r : ℕ) (e : Fin d → ℕ) :
    ((Fin (d + 1) → ℕ) → ℂ) → ((Fin (d + 1) → ℕ) → ℂ) :=
  rTensor fun i => negIdx (e i) ∘ synG r (e i)

/-- Fixed-point `G̃_{t_1,…,t_d}` (Proposition 3.3). -/
def synGad {d : ℕ} (r : ℕ) (e : Fin d → ℕ) :
    ((Fin (d + 1) → ℕ) → ℤ × ℤ) → ((Fin (d + 1) → ℕ) → ℤ × ℤ) :=
  rTensor fun i => synGa r (e i)

/-- Fixed-point `G̃*_{t_1,…,t_d}`. -/
def synGadInv {d : ℕ} (r : ℕ) (e : Fin d → ℕ) :
    ((Fin (d + 1) → ℕ) → ℤ × ℤ) → ((Fin (d + 1) → ℕ) → ℤ × ℤ) :=
  rTensor fun i => negIdx (e i) ∘ synGa r (e i)

/-- Coefficient `c` of the product of `∑ aᵢ yⁱ` and `∑ bᵢ yⁱ` in `ℂ[y]/(y^r + 1)`, `c < r`. -/
noncomputable def negaCoeff (r : ℕ) (a b : ℕ → ℂ) (c : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (c + 1), a i * b (c - i) - ∑ i ∈ Finset.Ico (c + 1) r, a i * b (c + r - i)

/-- Exact normalised pointwise product `(u_j v_j)/r` of two arrays over `R` (zero past the
coefficient range). -/
noncomputable def mulPt {d : ℕ} (r : ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ) (j : Fin (d + 1) → ℕ) : ℂ :=
  if j (Fin.last d) < r then
    negaCoeff r (fun c => u (Function.update j (Fin.last d) c))
      (fun c => v (Function.update j (Fin.last d) c)) (j (Fin.last d)) / r
  else 0

/-- The coefficient list (length `r`) of the `R`-entry of `x` at position `j`. -/
def coeffList {β : Type*} {d : ℕ} (r : ℕ) (x : (Fin (d + 1) → ℕ) → β) (j : Fin (d + 1) → ℕ) :
    List β :=
  (List.range r).map fun c => x (Function.update j (Fin.last d) c)

/-- Fixed-point pointwise product via Lemma 2.5 (`mulR`, Kronecker substitution). -/
def mulPtZ {d : ℕ} (p r : ℕ) (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) (j : Fin (d + 1) → ℕ) : ℤ × ℤ :=
  (mulR p r ((coeffList r U j).map Prod.fst) ((coeffList r U j).map Prod.snd)
    ((coeffList r V j).map Prod.fst) ((coeffList r V j).map Prod.snd)).getD (j (Fin.last d)) (0, 0)

/-- Lemma 2.2 for `c = 2^k`: multiply by `2^k`, and if the result leaves the disc of radius `2^p`,
pull it back by the factor `2^p / ⌈|w|⌉`, rounding towards zero. -/
def scaleZ (p k : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  let w : ℤ × ℤ := (2 ^ k * z.1, 2 ^ k * z.2)
  if w.1 ^ 2 + w.2 ^ 2 ≤ 4 ^ p then w
  else
    let m : ℤ := ceilSqrt (w.1 ^ 2 + w.2 ^ 2).toNat
    ((w.1 * 2 ^ p).tdiv m, (w.2 * 2 ^ p).tdiv m)

/-- Proposition 3.4, algorithm: `M̃_R(U, V) = scale_{T/r}(G̃*(Ã(G̃U, G̃V)))`, where `T/r = 2^{∑ eᵢ}`. -/
def convRa {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) :
    (Fin (d + 1) → ℕ) → ℤ × ℤ :=
  fun j => scaleZ p (∑ i, e i) (synGadInv r e (mulPtZ p r (synGad r e U) (synGad r e V)) j)

/-- The exact normalised convolution `M_R(u, v) = (1/T) u ∗ v` over `R`, for in-range indices:
cyclic in each `R`-axis (length `2^{eᵢ}`), negacyclic in `y`. Here `T = r ∏ 2^{eᵢ}`. -/
noncomputable def convR {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) : ℂ :=
  (1 / (r * 2 ^ (∑ i, e i)) : ℂ) *
    ∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
      negaCoeff r
        (fun c => u (Fin.snoc (fun i => k i) c))
        (fun c => v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c))
        (j (Fin.last d))

end IntMul.HvdH


