-- Prove2me | Definitions.Def_FourierDimTesting102_Quantum_Supplement_Algorithms
-- name    : FourierDimTesting102_Quantum_Supplement_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:26:35.697199+00:00
-- url     : https://prove2.me/theorems/a477016b-8657-47fd-b917-e8f8131aed3f
-- title:
--   Algorithm 2 and Algorithm 4: classical testers for Fourier dimensionality
-- statement:
--   This file fixes the two classical algorithms of the paper as nonadaptive randomized query algorithms, each determined by $n$, $k$, $\epsilon$ (and $\alpha$) before $f$ is seen.
--
--   **Algorithm 2** (p.19). Set $\ell$ to the least integer with $\binom{\ell}{2}\ge2^{k-1}$, $\lambda=\binom{\ell}{2}/2^k$, $\tau=(1-e^{-\lambda}+0.51\lambda)/2$, $m=\lceil(k\ln2+\ln100)/\epsilon\rceil$ and $T=1000$. In each of $T$ rounds, sample shifts $h_1,\dots,h_m$ and points $x_1,\dots,x_\ell$ independently and uniformly from $\mathbb F_2^n$, query
--
--   $$
--   \Phi(x_i)=(f(x_i+h_1),\dots,f(x_i+h_m))\quad(1\le i\le\ell),
--   $$
--
--   and record “A” if $\Phi(x_i)=\Phi(x_j)$ for some $i\neq j$. Accept if the number of rounds recording “A” is at least $\tau T$. It makes $Tm\ell$ queries.
--
--   **Algorithm 4** (p.31). Let $d=1-2\alpha$. Set $\ell$ as above, $p=1-\prod_{i=0}^{\ell-1}(1-i/2^k)$, $\tau=\frac{1+6\alpha}{2}\epsilon$, the dimension $r=k+1+\lceil\log_2(1000\binom{M}{k+1})\rceil$ with $M=\lceil4096((k+1)\ln(e/b)+\ln1000)/b^2\rceil$ and $b=\min(\epsilon d,1/2)$, and $T=\lceil\max(1600,\,32(kr\ln2+\ln100))/(p\epsilon d^2)\rceil$. For every $k$-dimensional subspace $W\le\mathbb F_2^r$ fix a basis $w_1,\dots,w_k$ and write $\Phi_W(a)=(\langle w_1,a\rangle,\dots,\langle w_k,a\rangle)$. Sample a uniformly random linear map $X:\mathbb F_2^n\to\mathbb F_2^r$. In each round $t$ sample $x_t\in\mathbb F_2^n$ and $a_{t,1},\dots,a_{t,\ell}\in\mathbb F_2^r$ uniformly and query $f(x_t+X^\top a_{t,i})$ for all $i$. For each $W$, $Z_{t,W}=0$ if no pair $i<j$ has $\Phi_W(a_{t,i})=\Phi_W(a_{t,j})$, and otherwise $Z_{t,W}=\mathbf 1[f(x_t+X^\top a_{t,i})\ne f(x_t+X^\top a_{t,j})]$ for the lexicographically first such pair. Accept if some $W$ has
--
--   $$
--   \hat\mu_X(W)=\frac{2}{pT}\sum_{t=1}^TZ_{t,W}\le\tau .
--   $$
--
--   It makes $T\ell$ queries; one set of queries per round serves every $W$.
--
--   For $\epsilon>1/2$ both algorithms run no rounds and accept: no function is at distance more than $1/2$ from the constant functions, so there is nothing to reject.
--
--   **Formalization Note** The source writes $T=O(1)$, $m=O(k/\epsilon)$, $\ell=O(2^{k/2})$ for Algorithm 2 and $r=O(k\log\frac1{\epsilon(1-2\alpha)})$, $\ell=O(2^{k/2})$, $T=O(\frac{kr}{\epsilon(1-2\alpha)^2})$ for Algorithm 4; the numerals above instantiate these and are not printed in the paper, while $\lambda$, $\tau$ and $p$ are exactly as printed. The basis of each $W$ is Lean's choice, which the source allows (“this choice can be arbitrary”); the lexicographic pair rule is the source's own example of an admissible rule.
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.19 Algorithm 2, p.31 Algorithm 4 (with its parameters, line 1), pp.27–29 §6.1

import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Model

/-!
# Supplement: Algorithm 2 and Algorithm 4 as nonadaptive classical query algorithms

Kenny Chen, *Exponential Quantum Advantage in Testing Fourier Dimensionality*, September 2026
STOC 2027 submission #102 preprint, Algorithm 2 (p.19), Algorithm 4 (p.31), Lemma 6.3 (p.31),
§6.1 (pp.27–29).

Both algorithms are fixed from `n`, `k`, `ε` (and `α`) alone; `f` enters only through the
answers at the query points. The numerals in `alg2T`, `alg2m`, `alg2ell`, `compM`, `compR` and
`alg4T` instantiate the source's unspecified `O(·)`; `λ`, `τ` and `p` are exactly as printed.
For `ε > 1/2` no function is `ε`-far from `D_k` (a constant function is within `1/2`), and both
algorithms run zero rounds and accept.
-/

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-! ### Algorithm 2 (p.19) -/

theorem exists_ell (k : ℕ) : ∃ ℓ : ℕ, 2 ^ k ≤ 2 * ℓ.choose 2 :=
  ⟨2 ^ k + 1, by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    exact le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_left _ two_pos)⟩

open Classical in
/-- `ℓ = O(2^{k/2})`: the least `ℓ` with `\binom{ℓ}{2} ≥ 2^{k-1}`, so that `λ ∈ [1/2, 1]`. -/
noncomputable def alg2ell (k : ℕ) : ℕ := Nat.find (exists_ell k)

/-- `λ = \binom{ℓ}{2} / 2^k`, as printed in line 1 of Algorithm 2. -/
noncomputable def lam (k ℓ : ℕ) : ℝ := (ℓ.choose 2 : ℝ) / 2 ^ k

/-- `τ = (1 − e^{−λ} + 0.51 λ)/2`, as printed in line 1 of Algorithm 2. -/
noncomputable def tau2 (k ℓ : ℕ) : ℝ := (1 - Real.exp (-lam k ℓ) + 0.51 * lam k ℓ) / 2

/-- `m = O(k/ε)`: `m = ⌈(k ln 2 + ln 100)/ε⌉`. -/
noncomputable def alg2m (k : ℕ) (ε : ℝ) : ℕ := ⌈((k : ℝ) * Real.log 2 + Real.log 100) / ε⌉₊

open Classical in
/-- `T = O(1)`: `T = 1000` rounds, and no rounds when `ε > 1/2`. -/
noncomputable def alg2T (ε : ℝ) : ℕ := if 1 / 2 < ε then 0 else 1000

/-- The seed of Algorithm 2: for each round `t`, the shifts `h₁, …, h_m` and the points
`x₁, …, x_ℓ`, all independent and uniform on `F₂ⁿ`. -/
abbrev Alg2Seed (n k : ℕ) (ε : ℝ) :=
  Fin (alg2T ε) → (Fin (alg2m k ε) → V n) × (Fin (alg2ell k) → V n)

/-- The queries of Algorithm 2: in round `t`, the value `f(x_i + h_j)` for every `i` and `j`. -/
abbrev Alg2Query (k : ℕ) (ε : ℝ) := Fin (alg2T ε) × Fin (alg2ell k) × Fin (alg2m k ε)

open Classical in
/-- Algorithm 2, p.19. Round `t` queries `Φ(x_i) = (f(x_i + h_1), …, f(x_i + h_m))` for every `i`
and records "A" when `Φ(x_i) = Φ(x_j)` for some `i ≠ j`; the algorithm accepts (`true`) when the
number of rounds recording "A" is at least `τ · T`. -/
noncomputable def alg2 (n k : ℕ) (ε : ℝ) :
    NonadaptiveRandAlg n (Alg2Seed n k ε) (Alg2Query k ε) where
  pts := fun r q => (r q.1).2 q.2.1 + (r q.1).1 q.2.2
  dec := fun _ a =>
    decide (tau2 k (alg2ell k) * (alg2T ε : ℝ) ≤
      ((Finset.univ.filter fun t : Fin (alg2T ε) =>
        ∃ i j : Fin (alg2ell k), i ≠ j ∧ (fun h => a (t, i, h)) = (fun h => a (t, j, h))).card : ℝ))

/-! ### Algorithm 4 (p.31) -/

/-- The `k`-dimensional linear subspaces of `F₂ʳ`, the subspaces Algorithm 4 enumerates. -/
abbrev KSub (r k : ℕ) := {W : Submodule (ZMod 2) (V r) // Module.finrank (ZMod 2) W = k}

/-- Line 2 of Algorithm 4: a basis `{w₁, …, w_k}` of `W`, chosen once and arbitrarily. -/
noncomputable def kBasis {r k : ℕ} (W : KSub r k) : Module.Basis (Fin k) (ZMod 2) W.1 :=
  Module.finBasisOfFinrankEq (ZMod 2) W.1 W.2

/-- Line 7 of Algorithm 4: `Φ_W(a) = (⟨w₁, a⟩, …, ⟨w_k, a⟩)`. -/
noncomputable def phiW {r k : ℕ} (W : KSub r k) (a : V r) : Fin k → ZMod 2 :=
  fun i => ((kBasis W i : W.1) : V r) ⬝ᵥ a

open Classical in
/-- Line 9 of Algorithm 4: the lexicographically first pair `i < j` with `Φ_W(a_i) = Φ_W(a_j)`,
or `none` when there is no such pair (event `C_W` fails). The choice depends only on the labels
`Φ_W(a_i)`. -/
noncomputable def firstCollision {r k ℓ : ℕ} (W : KSub r k) (a : Fin ℓ → V r) :
    Option (Fin ℓ × Fin ℓ) :=
  (List.product (List.finRange ℓ) (List.finRange ℓ)).find? fun p =>
    decide (p.1 < p.2 ∧ phiW W (a p.1) = phiW W (a p.2))

/-- Line 9 of Algorithm 4: `Z_W = 0` without a collision, otherwise the disagreement indicator
`1[b_i ≠ b_j]` of the answers `b_i = f(x + Xᵀ a_i)` at the first colliding pair. -/
noncomputable def zVal {r k ℓ : ℕ} (W : KSub r k) (a : Fin ℓ → V r) (b : Fin ℓ → Bool) : ℝ :=
  match firstCollision W a with
  | none => 0
  | some p => if b p.1 ≠ b p.2 then 1 else 0

/-- The query point `x + Xᵀ a`. -/
def shiftPt {n r : ℕ} (X : LinMap n r) (x : V n) (a : V r) : V n :=
  x + X.transpose.mulVec a

/-- `p = 1 − ∏_{i=0}^{ℓ−1} (1 − i/2^k)`, as printed in line 1 of Algorithm 4. -/
noncomputable def pColl (k ℓ : ℕ) : ℝ := 1 - ∏ i ∈ Finset.range ℓ, (1 - (i : ℝ) / 2 ^ k)

/-- `τ = (1 + 6α)ε/2`, as printed in line 1 of Algorithm 4. -/
noncomputable def tau4 (α ε : ℝ) : ℝ := (1 + 6 * α) / 2 * ε

/-- The sample size `M = ⌈4096((k+1) ln(e/b) + ln 1000)/b²⌉` of Lemma 6.1, failure `1/1000`. -/
noncomputable def compM (k : ℕ) (b : ℝ) : ℕ :=
  ⌈4096 * (((k : ℝ) + 1) * Real.log (Real.exp 1 / b) + Real.log 1000) / b ^ 2⌉₊

/-- The compression dimension `r = k + 1 + ⌈log₂(1000 · \binom{M}{k+1})⌉` of Lemma 6.2 for that
`M`, failure `1/1000`; it is `O(k log(1/b))` (Theorem 6.1). -/
noncomputable def compR (k : ℕ) (b : ℝ) : ℕ :=
  k + 1 + ⌈Real.logb 2 (1000 * ((compM k b).choose (k + 1) : ℝ))⌉₊

/-- `r = O(k log(1/(ε(1−2α))))` of line 1 of Algorithm 4: the compression schedule at
`β = min(ε(1 − 2α), 1/2)`; it satisfies `r ≥ k + 1`. -/
noncomputable def alg4r (k : ℕ) (α ε : ℝ) : ℕ := compR k (min (ε * (1 - 2 * α)) (1 / 2))

open Classical in
/-- `T = O(kr/(ε(1−2α)²))`: `T = ⌈max(1600, 32(kr ln 2 + ln 100))/(p ε (1−2α)²)⌉`, and no rounds
when `ε > 1/2`. -/
noncomputable def alg4T (k : ℕ) (α ε : ℝ) : ℕ :=
  if 1 / 2 < ε then 0 else
    ⌈max 1600 (32 * ((k : ℝ) * (alg4r k α ε : ℝ) * Real.log 2 + Real.log 100)) /
      (pColl k (alg2ell k) * ε * (1 - 2 * α) ^ 2)⌉₊

/-- The seed of Algorithm 4: the linear map `X : F₂ⁿ → F₂ʳ`, then for each round `t` the point
`x_t ∈ F₂ⁿ` and `a_{t,1}, …, a_{t,ℓ} ∈ F₂ʳ`, all independent and uniform. -/
abbrev Alg4Seed (n k : ℕ) (α ε : ℝ) :=
  LinMap n (alg4r k α ε) × (Fin (alg4T k α ε) → V n × (Fin (alg2ell k) → V (alg4r k α ε)))

/-- The queries of Algorithm 4: in round `t`, the value `f(x_t + Xᵀ a_{t,i})` for every `i`. -/
abbrev Alg4Query (k : ℕ) (α ε : ℝ) := Fin (alg4T k α ε) × Fin (alg2ell k)

/-- Line 11 of Algorithm 4: `μ̂_X(W) = (2/(pT)) ∑_t Z_{t,W}`. -/
noncomputable def muHat {n k : ℕ} {α ε : ℝ} (W : KSub (alg4r k α ε) k) (r : Alg4Seed n k α ε)
    (a : Alg4Query k α ε → Bool) : ℝ :=
  2 / (pColl k (alg2ell k) * (alg4T k α ε : ℝ)) *
    ∑ t : Fin (alg4T k α ε), zVal W (r.2 t).2 (fun i => a (t, i))

open Classical in
/-- Algorithm 4, p.31. One set of `ℓ` queries per round serves every `k`-dimensional `W ≤ F₂ʳ`;
the algorithm accepts (`true`) when some `W` has `μ̂_X(W) ≤ τ` (or when it runs no rounds). -/
noncomputable def alg4 (n k : ℕ) (α ε : ℝ) :
    NonadaptiveRandAlg n (Alg4Seed n k α ε) (Alg4Query k α ε) where
  pts := fun r q => shiftPt r.1 (r.2 q.1).1 ((r.2 q.1).2 q.2)
  dec := fun r a =>
    decide (alg4T k α ε = 0 ∨ ∃ W : KSub (alg4r k α ε) k, muHat W r a ≤ tau4 α ε)

end FourierDimTesting102.Quantum.Supplement


