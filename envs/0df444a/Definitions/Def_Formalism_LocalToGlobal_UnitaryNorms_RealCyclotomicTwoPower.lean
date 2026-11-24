-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
-- name    : Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:03.424655+00:00
-- url     : https://prove2.me/theorems/d23896f4-5687-472b-8a4e-c864c2094a65
-- title:
--   Real Cyclotomic Two Power
-- statement:
--   Definitions and structural lemmas for Real Cyclotomic Two Power, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RealCyclotomicTwoPower.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
namespace Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
abbrev Qb : Type := AlgebraicClosure ℚ
abbrev Fld : Type := IntermediateField ℚ Qb
def sqrts (m : ℤ) : Set Qb := {z | z ^ 2 = (m : Qb)}
def mus (N : ℕ) : Set Qb := {z | z ^ N = 1}
def sqQ (m : ℤ) : Fld := adjoin ℚ (sqrts m)
def cycQ (N : ℕ) : Fld := adjoin ℚ (mus N)
def cycQplus (N : ℕ) : Fld := adjoin ℚ ((fun z => z + z⁻¹) '' mus N)
def KQ (d : ℕ) : Fld := sqQ (-(d : ℤ))
def biquadraticField (q d : ℕ) : Fld := sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ))
def realCyclotomicTwoPower (e : ℕ) : Fld := cycQplus (2 ^ (e + 2))
def EQ (e q d : ℕ) : Fld := biquadraticField q d ⊔ realCyclotomicTwoPower e
def FQ (e q d : ℕ) : Fld := sqQ ((q : ℤ) * (d : ℤ)) ⊔ realCyclotomicTwoPower e
def LQ (e q d : ℕ) : Fld := biquadraticField q d ⊔ cycQ (2 ^ (e + 2))
abbrev GalOf (L : Fld) : Subgroup (Qb ≃ₐ[ℚ] Qb) := L.fixingSubgroup
def restr (L : Fld) (s : Qb ≃ₐ[ℚ] Qb) : L →ₐ[ℚ] Qb := (s : Qb →ₐ[ℚ] Qb).comp L.val
def ActsAs (e q d : ℕ) (s : EQ e q d →ₐ[ℚ] Qb) (g : GG e) : Prop :=
  (∀ x : EQ e q d, (x : Qb) ∈ sqrts (-(q : ℤ)) → s x = (((g.1.1 : ℤˣ) : ℤ) : Qb) * x) ∧
  (∀ x : EQ e q d, (x : Qb) ∈ sqrts (-(d : ℤ)) → s x = (((g.1.2 : ℤˣ) : ℤ) : Qb) * x) ∧
  ∃ u : (ZMod (2 ^ (e + 2)))ˣ, hcl e u = g.2 ∧
    ∀ (x : EQ e q d) (z : Qb), z ∈ mus (2 ^ (e + 2)) → (x : Qb) = z + z⁻¹ →
      s x = z ^ (u : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val
def condN (e q d : ℕ) : ℕ := 2 ^ (e + 2) * q * d
def IsCond (L : Fld) (N : ℕ) : Prop := L ≤ cycQ N ∧ ∀ M : ℕ, 0 < M → L ≤ cycQ M → N ∣ M
open Classical in

def sqSign {p : ℕ} (u : (ZMod p)ˣ) : ℤˣ := if IsSquare (u : ZMod p) then 1 else -1
theorem q_dvd_condN (e q d : ℕ) : q ∣ condN e q d := by
  unfold condN
  exact dvd_mul_of_dvd_left (dvd_mul_left q _) d
theorem d_dvd_condN (e q d : ℕ) : d ∣ condN e q d := by
  unfold condN
  exact dvd_mul_left d _
theorem two_pow_dvd_condN (e q d : ℕ) : 2 ^ (e + 2) ∣ condN e q d := by
  unfold condN
  exact dvd_mul_of_dvd_left (dvd_mul_right _ q) d
def artN (e : ℕ) {q d N : ℕ} (hq : q ∣ N) (hd : d ∣ N) (h2 : 2 ^ (e + 2) ∣ N) (u : (ZMod N)ˣ) : GG e :=
  ((sqSign (ZMod.unitsMap hq u), sqSign (ZMod.unitsMap hd u)), hcl e (ZMod.unitsMap h2 u))
def artGG (e q d : ℕ) (u : (ZMod (condN e q d))ˣ) : GG e :=
  artN e (q_dvd_condN e q d) (d_dvd_condN e q d) (two_pow_dvd_condN e q d) u
def CondEQ (e q d : ℕ) : Prop := IsCond (EQ e q d) (condN e q d)
def ArtinEQ (e q d : ℕ) : Prop :=
  ∀ (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod (condN e q d))ˣ),
    (∀ z ∈ mus (condN e q d), s z = z ^ (u : ZMod (condN e q d)).val) →
    ActsAs e q d (restr (EQ e q d) s) (artGG e q d u)
end Formalism.L2.Host


