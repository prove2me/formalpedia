-- Prove2me | Definitions.Def_GraphSimOT_Gaps_CutRounding
-- name    : GraphSimOT_Gaps_CutRounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:46.461368+00:00
-- url     : https://prove2.me/theorems/d7f7c7f4-e49d-4da4-9bf3-b180a0547fad
-- title:
--   ζ_Q, α-thin permutation matrices, the thinness constant, the spectral surrogate of ζ_Q, zonotopes Z_Q, support functions h_Q and ρ (App. E.2)
-- statement:
--   Objects of the rounding arguments for the cut distance (App. E.2). Graphs $G, H$ on $[n]$ have adjacency matrices $A, B$.
--
--   For $Q\in\mathrm{DS}(n)$ (Eq. (21)),
--   $$\zeta_Q = \max_{S,T\subseteq[n]^2}\frac1{n^2}\Big|\sum_{(i,j)\in S}\sum_{(k,\ell)\in T}Q_{ij}Q_{k\ell}(A_{ik} - B_{j\ell})\Big| = n^{-2}\,\|B(G,H,Q)\|_\square$$
--   (`zeta`); $\delta^{OT}_\square = \min_Q\zeta_Q$ and $\delta_\square = \min_P\zeta_P$ over permutation matrices.
--
--   For $\alpha>0$, a matrix $P$ is **$\alpha$-thin with respect to $Q$** (Eq. (23), `IsThin α P Q`) if for all $X, Y\subseteq[n]$
--   $$\sum_{(i,j)\in(X\times\bar Y)\cup(\bar X\times Y)}P_{ij}\ \le\ \alpha\sum_{(i,j)\in(X\times\bar Y)\cup(\bar X\times Y)}Q_{ij},$$
--   with $\bar X = [n]\setminus X$ (`crossWeight`). A real $C$ is a **thinness constant** (`IsThinConstant C`) if for every $n\ge2$ every $Q\in\mathrm{DS}(n)$ admits an $\alpha$-thin permutation matrix with respect to $Q$ with $\alpha\le C\ln(2n)\ln\ln(4n)$; Theorem 35 asserts that some $C>0$ is one.
--
--   For vectors $z_{ij}\in\mathbb R^m$ ($i,j\in[n]$, standard inner product) and a linear operator $T$ on $\mathbb R^m$, the surrogate of Eq. (30) is
--   $$\max_{S,T'\subseteq[n]^2}\frac1{n^2}\Big|\sum_{(i,j)\in S}\sum_{(k,\ell)\in T'}Q_{ij}Q_{k\ell}\langle z_{ij}, T z_{k\ell}\rangle\Big|$$
--   (`zetaSpec`). The zonotope $Z_Q = \{\frac1n\sum_{i,j}Q_{ij}a_{ij}z_{ij} : a_{ij}\in[0,1]\}$ (Eq. (32), `zonotope`) has support function $h_Q(w) = \max_{u\in Z_Q}\langle w,u\rangle$ (Eq. (33), `suppFn`; the paper notes $h_Q(w) = \frac1n\sum_{i,j}Q_{ij}(\langle w, z_{ij}\rangle)_+$), and
--   $$\rho(Q,Q') = \sup_{\|w\|\le1}|h_Q(w) - h_{Q'}(w)|$$
--   (Eq. (34), `rhoZ`), the supremum over the closed unit ball.
--
--   **Formalization Note.** The cut norms are the published `FriezeKannan.CutDecomp.cutNorm` on matrices indexed by `Fin n × Fin n`. $h_Q$ and $\rho$ are suprema of nonempty bounded sets (the zonotope contains $0$ and is bounded; the unit ball contains $0$), so `sSup`/`⨆` are the true maxima/suprema. $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`.
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), App. E.2, p. 32 Eqs. (21), (23), Theorem 35; p. 39 Eq. (30); p. 40 Eqs. (32)–(34)

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting
import Definitions.Def_GraphSimOT_Gaps_Distances

open Matrix

namespace GraphSimOT.Gaps

/-!
# Objects of the cut rounding (App. E.2)

Breitung, Gervens, Grohe, *Graph Similarity Meets Optimal Transport*, arXiv:2611.05048
(held version, sha256 1cd10e91…), App. E.2, pp. 32–41.

* `zeta G H Q = ζ_Q` (Eq. (21)): the normalised cut norm `n^{-2} ‖B(G, H, Q)‖_□`.
* `IsThin α P Q`: `P` is `α`-thin with respect to `Q` (Eq. (23)).
* `IsThinConstant C`: `C` satisfies the conclusion of Theorem 35 (every `Q ∈ DS(n)`, `n ≥ 2`,
  admits a `C ln(2n) ln ln(4n)`-thin permutation matrix).
* `zetaSpec z T Q`: the bilinear surrogate of `ζ_Q` in Eq. (30).
* `zonotope z Q = Z_Q` (Eq. (32)), its support function `suppFn z Q = h_Q` (Eq. (33)), and the
  pseudometric `rhoZ z Q Q' = ρ(Q, Q')` (Eq. (34)), for vectors `z i j ∈ ℝ^m` (Euclidean).
-/

/-- `ζ_Q = max_{S,T ⊆ [n]²} n^{-2} |∑_{(i,j) ∈ S, (k,ℓ) ∈ T} Q_ij Q_kℓ (A_ik − B_jℓ)|`
(Eq. (21)), i.e. `n^{-2}` times the cut norm of `B(G, H, Q)`. -/
noncomputable def zeta {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) / (n : ℝ) ^ 2

/-- `∑_{(i,j) ∈ (X × Ȳ) ∪ (X̄ × Y)} M_ij`, the weight of `M` across the cut given by
`X, Y ⊆ [n]` (the two parts of the union are disjoint). -/
def crossWeight {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (X Y : Finset (Fin n)) : ℝ :=
  ∑ i ∈ X, ∑ j ∈ Yᶜ, M i j + ∑ i ∈ Xᶜ, ∑ j ∈ Y, M i j

/-- For `α > 0`, `P` is `α`-thin with respect to `Q` (Eq. (23)): for all `X, Y ⊆ [n]`,
`∑_{(X×Ȳ) ∪ (X̄×Y)} P_ij ≤ α ∑_{(X×Ȳ) ∪ (X̄×Y)} Q_ij`. -/
def IsThin {n : ℕ} (α : ℝ) (P Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  0 < α ∧ ∀ X Y : Finset (Fin n), crossWeight P X Y ≤ α * crossWeight Q X Y

/-- `C` has the property of the constant `C_thin` of Theorem 35: for every `n ≥ 2` (the standing
assumption of App. E.2) every `Q ∈ DS(n)` admits an `α`-thin permutation matrix with respect
to `Q` with `α ≤ C ln(2n) ln ln(4n)`. -/
def IsThinConstant (C : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ Q ∈ doublyStochastic ℝ (Fin n), ∃ α : ℝ,
    α ≤ C * Real.log (2 * n) * Real.log (Real.log (4 * n)) ∧
    ∃ π : Equiv.Perm (Fin n), IsThin α (π.permMatrix ℝ) Q

/-- The surrogate of Eq. (30):
`max_{S,T ⊆ [n]²} n^{-2} |∑_{(i,j) ∈ S} ∑_{(k,ℓ) ∈ T} Q_ij Q_kℓ ⟨z_ij, T z_kℓ⟩|`. -/
noncomputable def zetaSpec {n m : ℕ} (z : Fin n → Fin n → EuclideanSpace ℝ (Fin m))
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  FriezeKannan.CutDecomp.cutNorm
      (fun a b : Fin n × Fin n =>
        Q a.1 a.2 * Q b.1 b.2 * inner ℝ (z a.1 a.2) (T (z b.1 b.2))) / (n : ℝ) ^ 2

/-- The zonotope `Z_Q = {(1/n) ∑_{i,j} Q_ij a_ij z_ij : a_ij ∈ [0, 1]}` (Eq. (32)). -/
def zonotope {n m : ℕ} (z : Fin n → Fin n → EuclideanSpace ℝ (Fin m))
    (Q : Matrix (Fin n) (Fin n) ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {u | ∃ a : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ a i j ∧ a i j ≤ 1) ∧
    u = (1 / (n : ℝ)) • ∑ i, ∑ j, (Q i j * a i j) • z i j}

/-- The support function `h_Q(w) = max_{u ∈ Z_Q} ⟨w, u⟩` of the zonotope (Eq. (33); the paper
notes it equals `(1/n) ∑_{i,j} Q_ij (⟨w, z_ij⟩)_+` for `Q ∈ DS(n)`), written as the supremum
of the nonempty bounded set of values. -/
noncomputable def suppFn {n m : ℕ} (z : Fin n → Fin n → EuclideanSpace ℝ (Fin m))
    (Q : Matrix (Fin n) (Fin n) ℝ) (w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  sSup ((fun u => inner ℝ w u) '' zonotope z Q)

/-- The pseudometric `ρ(Q, Q') = sup_{w ∈ B_H} |h_Q(w) − h_{Q'}(w)|` (Eq. (34)), the supremum
over the closed unit ball of `ℝ^m`. -/
noncomputable def rhoZ {n m : ℕ} (z : Fin n → Fin n → EuclideanSpace ℝ (Fin m))
    (Q Q' : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ w : {w : EuclideanSpace ℝ (Fin m) // ‖w‖ ≤ 1}, |suppFn z Q w - suppFn z Q' w|

end GraphSimOT.Gaps


