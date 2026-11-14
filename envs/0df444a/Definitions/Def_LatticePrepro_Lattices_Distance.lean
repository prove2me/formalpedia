-- Prove2me | Definitions.Def_LatticePrepro_Lattices_Distance
-- name    : LatticePrepro_Lattices_Distance
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:22:49.369643+00:00
-- url     : https://prove2.me/theorems/9448ef8f-84ab-4977-9854-5384d43519a8
-- title:
--   Definition 3.1 — the $\ell_p$ distance from a target to a lattice
-- statement:
--   For a lattice family $(\Lambda,(t_x)_{x\in X})$, that is, a lattice $\Lambda\subseteq\mathbb Z^M$ with integer targets $t_x$, a norm exponent $p$ (a real $p\ge1$ or $p=\infty$) and an instance $x$, the definition `LatticeFamily.latticeDist` is
--   $$\operatorname{dist}_p(t_x,\Lambda)=\inf_{v\in\Lambda}\|t_x-v\|_p,$$
--   the distance from the target to the lattice, where $\|\cdot\|_p$ is the $\ell_p$ norm on $\mathbb R^M$. An accompanying instance records that $\Lambda$ is nonempty ($0\in\Lambda$), so the infimum is over a nonempty set.
--
--   This is the lattice half of Definition 3.1, $\operatorname{dist}_p(t,\mathcal L)=\min_{v\in\mathcal L}\|t-v\|_p$. The final lattice theorems (Theorem 5.1) and the notion of an $f$-approximate solution (Lemma 5.2) are stated with it.
--
--   **Formalization Note.** The infimum is `⨅ v : Λ.lattice, Λ.dist pn x v` in $\mathbb R$. The source module proves that it is attained (`exists_dist_eq_latticeDist`), so it agrees with the paper's minimum, and `Lattices/Mathlib.lean` identifies it with Mathlib's `Metric.infDist` in `PiLp`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definition 3.1 (\label{def:code-lattice-distances}); Lean: LatticePrepro/Lattices/Distance.lean, LatticePrepro.LatticeFamily.latticeDist

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

/-!
# Distance from a target to a lattice

The paper (Definition 3.1) measures the distance from a target `t` to a lattice `Λ` as
`dist_p(t, Λ) = min_{v ∈ Λ} ‖t − v‖_p`. For a `LatticeFamily`, we define
`latticeDist pn x = ⨅ v ∈ Λ, ‖t_x − v‖_p` and show that the infimum is attained
(`exists_dist_eq_latticeDist`): the lattice vectors within any given distance of `t_x` form a
finite set of integer vectors, since every coordinate is bounded by the `ℓ_p` norm.

The consequences `latticeDist_le_of_exists` and `lt_latticeDist_of_forall` translate the
"some lattice vector within `R`" / "every lattice vector beyond `γ R`" form of the main theorems
into bounds on `dist_p(t_x, Λ)`.
-/

namespace LatticePrepro

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X) (pn : PNorm) (x : X)

/-- The distance `dist_p(t_x, Λ) = inf_{v ∈ Λ} ‖t_x − v‖_p` from the target to the lattice
(Definition 3.1). The infimum is attained (`exists_dist_eq_latticeDist`). -/
noncomputable def latticeDist : ℝ := ⨅ v : Λ.lattice, Λ.dist pn x v

instance : Nonempty Λ.lattice := ⟨0⟩

end LatticeFamily

end LatticePrepro


