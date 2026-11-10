-- Prove2me | Definitions.Def_AlgCoverage_OddOrder_Series
-- name    : AlgCoverage_OddOrder_Series
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:45:34.748096+00:00
-- url     : https://prove2.me/theorems/51419a68-2269-4474-b28d-4057dbdcd0a8
-- title:
--   $G$-normal elementary-abelian series (6.1), layer coefficient maps and the test FULL
-- statement:
--   A **$G$-normal elementary-abelian series** of a group $G$ (6.1) is a chain
--   $$1=A_0\triangleleft A_1\triangleleft\cdots\triangleleft A_J=G,\qquad A_r\triangleleft G,\qquad A_r/A_{r-1}\cong\mathbb F_{p_r}^{d_r},$$
--   with every $p_r$ an odd prime and every layer nontrivial ($d_r\ge1$); $D=\max_r d_r$.
--
--   For inputs $x=(X_1,\dots,X_k)$ and a mask $v$, the prefix before position $i$ is $P_i=\prod_{h<i}X_h^{v_h}$ (input order). Conjugation $\theta$ makes each layer $A_r/A_{r-1}$ a $G$-module, and the **layer coefficient map** of a selector array $U=(v_u)_u$ sends lifts $(a_1,\dots,a_k)$ of the layer to the vector of layer words $\big(\sum_i v_{ui}\,\theta(P_{u,i})a_i\big)_u$; in multiplicative notation the $u$-th entry is $\prod_{i:v_{ui}=1}P_{u,i}a_iP_{u,i}^{-1}$ modulo $A_{r-1}$. Its coefficients are of form (5.1) with stream $U_i=\theta(X_i)$. The selector array **passes FULL** when this map is surjective at every layer of the supplied series.
--
--   **Formalization Note.** `NormalEASeries G` stores `J`, subgroups `A 0, …, A J` (`A 0 = ⊥`, `A J = ⊤`, monotone, each normal in `G`), and for each 0-based layer `r < J` (the paper's layer $r+1$) an odd prime `p r`, a dimension `d r ≥ 1` and a group isomorphism of `A (r+1) ⧸ (A r).subgroupOf (A (r+1))` with `Multiplicative (Fin (d r) → ZMod (p r))`. `LayerOnto s r x rows` says: every target `y` with entries in `A (r+1)` is hit modulo `A r` by the layer word of some lifts `a` with entries in `A (r+1)`; this is surjectivity of the induced map on the abelian layer. `FULL s x rows` is `LayerOnto` at every layer; rows may be indexed by any type (empty and repeated rows allowed).
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 7 (PDF 8), §2.3; p. 21 (PDF 22), §6, Eq. (6.1) and the definition of FULL

import Mathlib

namespace AlgCoverage.OddOrder

/-- A **`G`-normal elementary-abelian series** (6.1) (Lin, §6, printed p. 21 / PDF 22):
`1 = A₀ ◁ A₁ ◁ ⋯ ◁ A_J = G`, every `A_r` normal in `G`, and every layer
`A_{r+1}/A_r ≅ 𝔽_{p_r}^{d_r}` with `p_r` an odd prime and `d_r ≥ 1`.

Indexing: subgroups `A 0, …, A J` (values of `A` beyond `J` are irrelevant); the layer with index
`r < J` is `A (r+1) / A r`, i.e. the paper's layer `r + 1`, with prime `p r` and dimension `d r`. -/
structure NormalEASeries (G : Type*) [Group G] where
  /-- the number of layers `J` -/
  J : ℕ
  /-- the subgroups `A_0, …, A_J` -/
  A : ℕ → Subgroup G
  bot : A 0 = ⊥
  top : A J = ⊤
  mono : ∀ r, r < J → A r ≤ A (r + 1)
  normal : ∀ r, (A r).Normal
  /-- the prime of layer `r` -/
  p : ℕ → ℕ
  /-- the dimension of layer `r` -/
  d : ℕ → ℕ
  p_prime : ∀ r, r < J → (p r).Prime
  p_odd : ∀ r, r < J → Odd (p r)
  d_pos : ∀ r, r < J → 0 < d r
  /-- `A_{r+1}/A_r ≅ 𝔽_p^d` as groups (the vector space written multiplicatively). -/
  layer_iso : ∀ r, r < J →
    haveI : (A r).Normal := normal r
    Nonempty ((↥(A (r + 1)) ⧸ (A r).subgroupOf (A (r + 1))) ≃*
      Multiplicative (Fin (d r) → ZMod (p r)))

/-- `D = max_r d_r` (`0` for the empty series of the trivial group). -/
def NormalEASeries.D {G : Type*} [Group G] (s : NormalEASeries G) : ℕ :=
  (Finset.range s.J).sup s.d

/-- The prefix `∏_{h<i} X_h^{v_h}` of the word `W_v` before position `i` (in input order). -/
def wordPrefix {G : Type*} [Group G] {k : ℕ} (x : Fin k → G) (v : Fin k → Bool) (i : Fin k) : G :=
  (List.ofFn fun h : Fin k => if h < i ∧ v h = true then x h else 1).prod

/-- The layer-`r` coefficient map of a word, evaluated on lifts `a = (a₁, …, a_k)` of the layer:
`∏_{i : v_i = 1} P_i a_i P_i⁻¹` with `P_i = wordPrefix x v i`, i.e. `∑_i v_i θ(P_i) a_i` in the
additive notation of the layer `A_{r+1}/A_r` (θ = conjugation; the order of the product is irrelevant
modulo `A_r`). The coefficient of `a_i` is of form (5.1) with stream `U_i = θ(X_i)`. -/
def layerWord {G : Type*} [Group G] {k : ℕ} (x : Fin k → G) (v : Fin k → Bool) (a : Fin k → G) : G :=
  (List.ofFn fun i : Fin k =>
    if v i = true then wordPrefix x v i * a i * (wordPrefix x v i)⁻¹ else 1).prod

/-- Surjectivity of the coefficient map at layer `r` (the paper's layer `r+1`) for the selector rows
`rows : ι → {0,1}^k` and inputs `x`: every target `y : ι → A_{r+1}` is hit modulo `A_r` by some lift
`a ∈ A_{r+1}^k`. -/
def LayerOnto {G : Type*} [Group G] (s : NormalEASeries G) (r : ℕ) {ι : Type*} {k : ℕ}
    (x : Fin k → G) (rows : ι → Fin k → Bool) : Prop :=
  ∀ y : ι → G, (∀ u, y u ∈ s.A (r + 1)) →
    ∃ a : Fin k → G, (∀ i, a i ∈ s.A (r + 1)) ∧
      ∀ u, (layerWord x (rows u) a)⁻¹ * y u ∈ s.A r

/-- `FULL(U)` (§6, p. 21): for the selector array `rows` (rows indexed by any type `ι`; empty and
repeated rows allowed) and the inputs `x`, the coefficient map is surjective at every layer of the
supplied series `s`. -/
def FULL {G : Type*} [Group G] (s : NormalEASeries G) {ι : Type*} {k : ℕ}
    (x : Fin k → G) (rows : ι → Fin k → Bool) : Prop :=
  ∀ r, r < s.J → LayerOnto s r x rows

end AlgCoverage.OddOrder


