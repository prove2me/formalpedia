-- Prove2me | Definitions.Def_KServerConj_Hmat
-- name    : KServerConj_Hmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:59.276961+00:00
-- url     : https://prove2.me/theorems/21ae821b-be31-4903-8bf4-a79a1a82dc68
-- title:
--   The request matrices $H$, $\hat H$ and $\hat Q$, equations (18)–(19)
-- statement:
--   Let $k=m+1$, let $r\in M$ be the current request, and write each column as $q_x=(a_x,\hat q_x)$ with $a_x\in K$ its first coordinate and $\hat q_x\in K^{k-1}$ the rest; $\pi$ deletes the first coordinate. Define
--
--   $$h_x=z^{-d(r,x)}q_x,\qquad H=[h_x]_{x\in M},\qquad \hat H=[\pi h_x]_{x\in M},$$
--
--   and let $\hat Q$ be the bottom block of $Q$, the rows $e_ie_j$ with $2\le i\le j\le k$:
--
--   $$\hat Q=\big[\,z^{-d(x,y)}\,\hat q_x\hat q_y\,\big]_{x\le y}.$$
--
--   The minimum minor valuations $\mu(H)$, $\mu(\hat H)$, $\mu(\hat Q)$ bound the old potential, give the new potential, and give the extended cost (Lemmas 4.1–4.3).
--
--   **Formalization Note** The first coordinate is index $0$; rows of $\hat Q$ are unordered pairs of the remaining $m$ coordinates, and its columns unordered pairs of points, as for $Q$.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §4.1, equations (18)–(19), p.10 (pdf p.11)

import Mathlib
import Definitions.Def_KServerConj_K
import Definitions.Def_KServerConj_symProd

namespace KServerConj

/-!
# The three matrices associated with a request

Coester, Koutsoupias, Zbysiński, *The k-server conjecture is true*, arXiv:2609.15979 (version of
2026-11-03, sha256 7ca0380a…), §4.1, printed p.10 (PDF p.11), equations (18) and (19):

"Write q_x = (a_x, q̂_x) and let π : K^k → K^{k−1} delete the first coordinate. Define the weighted
columns and their projection by h_x = z^{−d(r,x)} q_x, H = [h_x]_{x∈M}, Ĥ = [πh_x]_{x∈M}. (18)
Let Q̂ be the bottom coordinate block of Q, consisting of the rows e_ie_j with 2 ≤ i ≤ j ≤ k:
Q̂ = [ z^{−d(x,y)} q̂_x q̂_y ]_{x≤y}. (19)"

**Formalization Note.** Here `k = m + 1`; the first coordinate is `0 : Fin (m+1)`, `π` is
`Fin.tail` (coordinates `i.succ`), and the rows of `Q̂` are the pairs `s(i, j) : Sym2 (Fin m)`,
i.e. the paper's `e_{i+2}e_{j+2}`. Columns of `Q̂` are indexed by `Sym2 M` as for `Q`.
-/

/-- `H = [z^{−d(r,x)} q_x]_{x∈M}` (18). -/
noncomputable def Hmat {m : ℕ} {M : Type*} [PseudoMetricSpace M] (q : M → Fin (m + 1) → K (m + 1) M)
    (r : M) : Matrix (Fin (m + 1)) M (K (m + 1) M) :=
  fun i x => zp (-dist r x) * q x i

/-- `Ĥ = [π(z^{−d(r,x)} q_x)]_{x∈M}` (18): `H` with its first row deleted. -/
noncomputable def Hhat {m : ℕ} {M : Type*} [PseudoMetricSpace M] (q : M → Fin (m + 1) → K (m + 1) M)
    (r : M) : Matrix (Fin m) M (K (m + 1) M) :=
  fun i x => zp (-dist r x) * q x i.succ

/-- `Q̂ = [z^{−d(x,y)} q̂_x q̂_y]_{x≤y}` (19), the rows of `Q` not involving `e₁`. -/
noncomputable def Qhat {m : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (m + 1) → K (m + 1) M) : Matrix (Sym2 (Fin m)) (Sym2 M) (K (m + 1) M) :=
  fun p c => Sym2.lift ⟨fun x y => zp (-dist x y) * symProd (Fin.tail (q x)) (Fin.tail (q y)) p, by
    intro x y
    dsimp only
    rw [dist_comm, symProd_comm]⟩ c

end KServerConj


