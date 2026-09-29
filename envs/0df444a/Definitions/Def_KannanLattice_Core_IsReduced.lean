-- Prove2me | Definitions.Def_KannanLattice_Core_IsReduced
-- name    : KannanLattice_Core_IsReduced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:11:44.509985+00:00
-- url     : https://prove2.me/theorems/dd07709f-7315-4656-b38b-def98507b6c0
-- title:
--   Definition 2.6 — reduced (Korkine–Zolotarev) basis
-- statement:
--   Let $v_1,\dots,v_n$ be linearly independent vectors of $\mathcal R^k$, with Gram–Schmidt numbers $v_i(j)$ and projected lattices $L_j(v_1,\dots,v_n)$ as in the lattice notation of the paper. The basis $v_1,\dots,v_n$ of $L(v_1,\dots,v_n)$ is **reduced** (Definition 2.6) if
--
--   $$v_j(j)=\Lambda_1\big(L_j(v_1,\dots,v_n)\big)\quad\text{for } j=1,\dots,n, \tag{2.7}$$
--
--   $$|v_i(j)|\le \tfrac12\, v_j(j)\quad\text{for } i\ge j+1\ge 2. \tag{2.8}$$
--
--   Condition (2.7) says that each Gram–Schmidt length is the length of a shortest nonzero vector of the corresponding projected lattice; in particular $v_1$ is a shortest nonzero vector of the whole lattice. Condition (2.8) is size reduction. Such bases go back to Korkine and Zolotareff (1873). In the paper a reduced basis of the lattice $\tau\mathbb Z^n$ is the starting point of the proof of Theorem (5.5), and reducedness is the standing hypothesis of the procedure CLP′ and of Proposition 4.3.
--
--   **Formalization Note** Indices are 0-based: (2.7) is `∀ j, gsLen b j = lambdaOne (projLattice b j)` and (2.8) is `∀ i j, j < i → |gsCoeff b i j| ≤ gsLen b j / 2`.
-- source:
--   Kannan, Minkowski's Convex Body Theorem and Integer Programming, Math. Oper. Res. 12 (1987); author's final manuscript (CMU-CS-96-105), p. 11, Definition 2.6, (2.7), (2.8)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

/-- A reduced basis in the sense of Definition 2.6 (Kannan 1987, p. 11), i.e. a
Korkine–Zolotarev basis. With 0-based indices:

* (2.7) for every `j`, `b_j(j) = Λ₁(L_j(b))`: the `j`-th Gram–Schmidt length is the length of a
  shortest nonzero vector of the projected lattice;
* (2.8) for `i > j`, `|b_i(j)| ≤ b_j(j)/2`. -/
def IsReduced {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) : Prop :=
  (∀ j : Fin m, gsLen b j = lambdaOne (projLattice b j)) ∧
  (∀ i j : Fin m, j < i → |gsCoeff b i j| ≤ gsLen b j / 2)

end KannanLattice.Core


