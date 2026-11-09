-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Kernel
-- name    : TwoMasterRoommates_Capped_Kernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:38:21.424871+00:00
-- url     : https://prove2.me/theorems/39c3509a-5bce-4884-a914-69653187309a
-- title:
--   Common-order marked completion with mandatory and optional inert tokens
-- statement:
--   A finite population is partitioned into active identities $W$, mandatory tokens $T$, and optional tokens $J$. All actives share one whole weak rank map $r$, and a marked subset $U\subseteq W$ may receive tokens. Each active $w$ has an arbitrary upper cap $c(w)$. All identities are covered by a perfect matching. Permitted edges are precisely active–active, marked–mandatory, marked–optional, and optional–optional. Mandatory means $J$ is empty.
--
--   Only pairs of distinct actives can block, using the original strict comparisons:
--
--   $$r(v)<r(Mu)\quad\text{and}\quad r(u)<r(Mv).$$
--
--   Every active must satisfy $r(Mw)\le c(w)$. Tokens are inert as blockers, but their ranks count as partner qualities. For $\ell\le |J|$, the prefix $P_\ell$ consists of the first $\ell$ optional identities ordered by $(r,\mathrm{ID})$. The prefix kernel is constructed on the subtype $W\cup T\cup P_\ell$, with selected optional identities made mandatory.
--
--   The bundle also provides comparison presentations, an integer input encoding, and the same two correct output branches as for the global problem. This kernel is a separate reusable completion object; its token permissions add no restrictions to the roommates instance.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), pp. 9–12 (PDF pp. 10–13), Appendix A, equation (2), Theorem A.1 and §A.4

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Encoding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

inductive Kind where
  | active | token | optional
  deriving DecidableEq, Repr

/-- The common-order kernel is independent of the two-master model. -/
structure Kernel (ι R : Type) [LinearOrder R] where
  kind : ι → Kind
  marked : ι → Bool
  r : ι → R
  c : ι → WithTop R

def Mandatory {ι R : Type} [LinearOrder R] (K : Kernel ι R) : Prop :=
  ∀ v, K.kind v ≠ .optional

def KPermitted {ι R : Type} [LinearOrder R] (K : Kernel ι R) (u v : ι) : Prop :=
  (K.kind u = .active ∧ K.kind v = .active) ∨
  (K.kind u = .active ∧ K.marked u = true ∧ K.kind v ≠ .active) ∨
  (K.kind v = .active ∧ K.marked v = true ∧ K.kind u ≠ .active) ∨
  (K.kind u = .optional ∧ K.kind v = .optional)

def KSolution {ι R : Type} [LinearOrder R] (K : Kernel ι R) (M : ι → ι) : Prop :=
  IsPerfectMatching M ∧ (∀ v, KPermitted K v (M v)) ∧
  (∀ w, K.kind w = .active → (K.r (M w) : WithTop R) ≤ K.c w) ∧
  ∀ u v, u ≠ v → K.kind u = .active → K.kind v = .active →
    ¬ (K.r v < K.r (M u) ∧ K.r u < K.r (M v))

def KSameComparisons {R : Type} [LinearOrder R] {m : ℕ}
    (K : Kernel (Fin m) R) (J : Kernel (Fin m) ℤ) : Prop :=
  K.kind = J.kind ∧ K.marked = J.marked ∧
  (∀ x y, K.r x < K.r y ↔ J.r x < J.r y) ∧
  ∀ w x, K.kind w = .active → ((K.r x : WithTop R) ≤ K.c w ↔ (J.r x : WithTop ℤ) ≤ J.c w)

def encodeKernel {m : ℕ} (K : Kernel (Fin m) ℤ) : List ℤ :=
  [(m : ℤ)] ++ (List.ofFn fun v => match K.kind v with | .active => (0 : ℤ) | .token => 1 | .optional => 2) ++
  (List.ofFn fun v => if K.marked v then (1 : ℤ) else 0) ++ List.ofFn K.r ++
  (List.ofFn K.c).flatMap encodeCap

def kstart {m : ℕ} (K : Kernel (Fin m) ℤ) : Light.State :=
  ⟨Light.frame [], Light.memOf (encodeKernel K)⟩

def KReports {R : Type} [LinearOrder R] {m : ℕ} (K : Kernel (Fin m) R)
    (S : ℕ) (σ : Light.State) : Prop :=
  (σ.loc 0 = 0 ∧ ¬ ∃ M, KSolution K M) ∨
  (0 < σ.loc 0 ∧ σ.loc 0 + (m : ℤ) ≤ (S : ℤ) ∧
    ∃ M, KSolution K M ∧ ∀ v, σ.mem ((σ.loc 0).toNat + v.val) = (M v).val)

noncomputable def optionalPrefix {ι R : Type} [Fintype ι] [LinearOrder ι] [LinearOrder R]
    (K : Kernel ι R) (l : ℕ) : Finset ι := by
  classical
  exact ((Finset.univ.filter fun v => K.kind v = .optional).toList.mergeSort
    (fun x y => decide (K.r x < K.r y ∨ (K.r x = K.r y ∧ x ≤ y)))).take l |>.toFinset

noncomputable def mandatoryPart {ι R : Type} [Fintype ι] [LinearOrder ι] [LinearOrder R]
    (K : Kernel ι R) (l : ℕ) : Finset ι := by
  classical
  exact (Finset.univ.filter fun v => K.kind v ≠ .optional) ∪ optionalPrefix K l

noncomputable def prefixKernel {ι R : Type} [Fintype ι] [LinearOrder ι] [LinearOrder R]
    (K : Kernel ι R) (l : ℕ) : Kernel {v // v ∈ mandatoryPart K l} R :=
  ⟨fun v => if K.kind v.val = .optional then .token else K.kind v.val,
   fun v => K.marked v.val, fun v => K.r v.val, fun v => K.c v.val⟩

end TwoMasterRoommates.Capped


