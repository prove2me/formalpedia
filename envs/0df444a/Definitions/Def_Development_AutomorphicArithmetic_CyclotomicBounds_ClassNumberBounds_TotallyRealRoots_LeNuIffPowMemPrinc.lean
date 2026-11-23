-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:42.589993+00:00
-- url     : https://prove2.me/theorems/5665b249-c3bf-4dc1-902f-c64387c1089e
-- title:
--   Le Nu Iff Pow Mem Princ
-- statement:
--   Definitions and structural lemmas for Le Nu Iff Pow Mem Princ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace KStar.TotallyRealRoots
variable (l : ℕ) [Fact l.Prime]
noncomputable def nu (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : ℕ∞ :=
  nuStar (l : ℤ_[l]) ((fun u : ℤ_[l]ˣ => (u : ℤ_[l])) '' (U : Set ℤ_[l]ˣ)) tr
noncomputable def redPow (a : ℕ) : ℤ_[l]ˣ →* (ZMod (l ^ a))ˣ :=
  Units.map (PadicInt.toZModPow a : ℤ_[l] →+* ZMod (l ^ a)).toMonoidHom
noncomputable def red : ℤ_[l]ˣ →* (ZMod l)ˣ :=
  Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom
noncomputable def princ (a : ℕ) : Subgroup ℤ_[l]ˣ := (redPow l a).ker
noncomputable def resOrder (U : Subgroup ℤ_[l]ˣ) : ℕ := Nat.card (U.map (red l))
noncomputable def depth (U : Subgroup ℤ_[l]ˣ) : ℕ∞ := nu l (U ⊓ princ l 1) 1
noncomputable def stdGroup (o a : ℕ) : Subgroup ℤ_[l]ˣ := rootsOfUnity o ℤ_[l] ⊔ princ l a
abbrev QmodZ : Type := ℚ_[l] ⧸ (1 : Submodule ℤ_[l] ℚ_[l])
def twistInv (A : Type*) [AddCommGroup A] [Module ℤ_[l] A] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) :
    Submodule ℤ_[l] A where
  carrier := {x | ∀ u ∈ U, ((u : ℤ_[l]) ^ tr) • x = x}
  zero_mem' := fun u _ => smul_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [smul_add, hx u hu, hy u hu]
  smul_mem' := fun c x hx u hu => by rw [smul_comm, hx u hu]
noncomputable def H0 (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : Submodule ℤ_[l] (QmodZ l) := twistInv l (QmodZ l) U tr
def TraceFixedResidues (N : ℕ) (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : AddSubgroup (ZMod (l ^ N)) where
  carrier := {x | ∀ u ∈ U, ((redPow l N u : (ZMod (l ^ N))ˣ) : ZMod (l ^ N)) ^ tr * x = x}
  zero_mem' := fun u _ => mul_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [mul_add, hx u hu, hy u hu]
  neg_mem' := fun {x} hx u hu => by rw [mul_neg, hx u hu]
noncomputable def levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) : Subgroup ℤ_[l]ˣ :=
  (H.map (ZMod.unitsMap (Nat.ordProj_dvd N l))).comap (redPow l (N.factorization l))
noncomputable def levelInertia (N : ℕ) : Subgroup (ZMod N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd N l)).ker
variable {l}
end KStar.TotallyRealRoots


