-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
-- name    : Formalism_SizeWindowBrackets_GaloisToProductIsIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:45:38.441982+00:00
-- url     : https://prove2.me/theorems/4b9eb532-4230-4cbe-b340-eded93912674
-- title:
--   Galois To Product Is Iso
-- statement:
--   Definitions and structural lemmas for Galois To Product Is Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/GaloisToProductIsIso.lean

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.LFunctionChainParameters.LHost
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
def localUnits (N p : ℕ) : Subgroup (ZMod N)ˣ := (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker
def IsFrobUnit (N p : ℕ) (w : (ZMod N)ˣ) : Prop :=
  ((w : ZMod N).cast : ZMod (ordCompl[p] N)) = (p : ZMod (ordCompl[p] N)) ∧
    ((w : ZMod N).cast : ZMod (ordProj[p] N)) = 1
def frobUnit (N p : ℕ) : (ZMod N)ˣ := by
  classical
  exact if h : ∃ w, IsFrobUnit N p w then h.choose else 1
section
variable {N : ℕ} {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def cftData (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) : ArithData H where
  q1 := q1
  d := d
  inertia p := Subgroup.toAddSubgroup' ((localUnits N p).map r)
  frob p := Multiplicative.toAdd (r (frobUnit N p))
def dirChar (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) : DirichletCharacter ℂ N :=
  MulChar.ofUnitHom (ψ.toMonoidHom.comp r).toHomUnits
end
def hostN (e q d : ℕ) : ℕ := 2 ^ (e + 2) * q * d
abbrev HA (e : ℕ) : Type := Additive (FrobeniusOrbits.HGrp e)
instance (e : ℕ) : Fintype (HA e) := Fintype.ofFinite _
instance (e : ℕ) : DecidableEq (HA e) := Classical.decEq _
def sgn2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun s := Multiplicative.ofAdd (if s = 1 then 0 else 1)
  map_one' := by simp
  map_mul' := by decide
def legU (N ℓ : ℕ) [Fact ℓ.Prime] (h : ℓ ∣ N) : (ZMod N)ˣ →* ℤˣ :=
  (quadraticChar (ZMod ℓ)).toUnitHom.comp (ZMod.unitsMap h)
theorem d_dvd_hostN (e q d : ℕ) : d ∣ hostN e q d := dvd_mul_left d _
theorem q_dvd_hostN (e q d : ℕ) : q ∣ hostN e q d :=
  dvd_mul_of_dvd_left (dvd_mul_left q _) d
theorem two_dvd_hostN (e q d : ℕ) : 2 ^ (e + 2) ∣ hostN e q d :=
  dvd_mul_of_dvd_left (dvd_mul_right _ q) d
def recMap (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] : (ZMod (hostN e q d))ˣ →* Multiplicative (E0 × HA e) where
  toFun u := Multiplicative.ofAdd
    ((Multiplicative.toAdd (sgn2 (legU _ d (d_dvd_hostN e q d) u)),
      Multiplicative.toAdd (sgn2 (legU _ q (q_dvd_hostN e q d) u))),
      Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u)))
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' u v := by
    simp only [map_mul]
    rfl
def hostData (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] : ArithData (HA e) := cftData q d (recMap e q d)
def FrobUnitSpec : Prop :=
  ∀ N p : ℕ, N ≠ 0 → p.Prime → IsFrobUnit N p (frobUnit N p) ∧ ∀ w, IsFrobUnit N p w → w = frobUnit N p
def UnramSpec : Prop :=
  ∀ N p : ℕ, N ≠ 0 → p.Prime → ¬ p ∣ N → localUnits N p = ⊥ ∧ ((frobUnit N p : (ZMod N)ˣ) : ZMod N) = (p : ZMod N)
section
variable (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H]
def DirCharSpec : Prop :=
  ∀ (N : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ),
    (∀ u : (ZMod N)ˣ, dirChar r ψ (u : ZMod N) = ψ (Multiplicative.toAdd (r u))) ∧
    ∀ x : ZMod N, ¬ IsUnit x → dirChar r ψ x = 0
def InertiaConductor : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (p : ℕ), N ≠ 0 → p.Prime →
    ((∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) ↔ ¬ p ∣ (dirChar r ψ).conductor)
def PrimValRamified : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (p i : ℕ), p.Prime → 1 ≤ i →
    ((∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) →
      primVal (cftData q1 d r) ψ (p ^ i) = ψ ((cftData q1 d r).frob p) ^ i) ∧
    ((¬ ∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) → primVal (cftData q1 d r) ψ (p ^ i) = 0)
def PrimValPrimitive : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (n : ℕ), N ≠ 0 → n ≠ 0 →
    primVal (cftData q1 d r) ψ n = (dirChar r ψ).primitiveCharacter (n : ZMod (dirChar r ψ).conductor)
end
def HostLocalParts : Prop :=
  ∀ e q d : ℕ, FrobeniusOrbits.HostHyp q d →
    (ordProj[2] (hostN e q d) = 2 ^ (e + 2) ∧ ordCompl[2] (hostN e q d) = q * d) ∧
    (ordProj[q] (hostN e q d) = q ∧ ordCompl[q] (hostN e q d) = 2 ^ (e + 2) * d) ∧
    (ordProj[d] (hostN e q d) = d ∧ ordCompl[d] (hostN e q d) = 2 ^ (e + 2) * q)
def RecKronecker : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
  ∀ (m : ℕ) (hm : m.Coprime (hostN e q d)) (hm2 : m.Coprime (2 ^ (e + 2))),
    ((Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime m hm))).1.1 = 0 ↔ jacobiSym (-(d : ℤ)) m = 1) ∧
    ((Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime m hm))).1.1 = 1 ↔ jacobiSym (-(d : ℤ)) m = -1) ∧
    ((Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime m hm))).1.2 = 0 ↔ jacobiSym (-(q : ℤ)) m = 1) ∧
    ((Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime m hm))).1.2 = 1 ↔ jacobiSym (-(q : ℤ)) m = -1) ∧
    (Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime m hm))).2
      = Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitOfCoprime m hm2))
def RecSurjective : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → Function.Surjective (recMap e q d)
def HostLocal : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
    (∀ (p : ℕ) (hp : p.Coprime (hostN e q d)), p.Prime → (hostData e q d).inertia p = ⊥ ∧
      (hostData e q d).frob p = Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime p hp))) ∧
    ((∀ x, x ∈ (hostData e q d).inertia 2 ↔ x.1 = 0) ∧ (hostData e q d).frob 2 = sg) ∧
    ((∀ x, x ∈ (hostData e q d).inertia q ↔ x = 0 ∨ x = sg) ∧
      ∀ hq : q.Coprime (2 ^ (e + 2)),
        (hostData e q d).frob q = ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitOfCoprime q hq)))) ∧
    ((∀ x, x ∈ (hostData e q d).inertia d ↔ x = 0 ∨ x = sgc0) ∧
      ∀ hd : d.Coprime (2 ^ (e + 2)),
        (hostData e q d).frob d = ((0, 1), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitOfCoprime d hd))))
def HostFactsHost : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → HostFacts (hostData e q d)
def ChConductor : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
    (dirChar (recMap e q d) chC).conductor = d ∧
    ∀ n : ℕ, n ≠ 0 → primVal (hostData e q d) chC n = ((jacobiSym (n : ℤ) d : ℤ) : ℂ)
def BalanceHost : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
  ∀ (ell : AddChar (E0 × HA e) ℂ → ℂ) (a : ℝ) (t : HA e) (w : E0 × HA e → ℝ),
    0 < a → (∀ ρ, InPhi ρ → 0 < w ρ) → ∀ N : ℕ, (∀ ρ, InPhi ρ → a / w ρ ≤ N) →
      (ASK (hostData e q d) N a t w : ℂ) - MAIN ell a w = De (hostData e q d) ell a t w
def galoisToProduct (e : ℕ) (g : FrobeniusOrbits.GG e) : E0 × HA e :=
  ((Multiplicative.toAdd (sgn2 g.1.2), Multiplicative.toAdd (sgn2 g.1.1)), Additive.ofMul g.2)
def GaloisToProductIsIso : Prop :=
  ∀ e : ℕ, Function.Bijective (galoisToProduct e) ∧ ∀ g g' : FrobeniusOrbits.GG e, galoisToProduct e (g * g') = galoisToProduct e g + galoisToProduct e g'
open NumberField Ideal in

def HostDataField : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), TwoAdicCyclotomicDecomposition.IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (FrobeniusOrbits.hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : FrobeniusOrbits.hostE ζ a b ≃ₐ[ℚ] FrobeniusOrbits.hostE ζ a b),
    ((∀ x : 𝓞 (FrobeniusOrbits.hostE ζ a b), σ • x - x ∈ P) ↔
      galoisToProduct e (FrobeniusOrbits.galE e ζ a b σ) ∈ (hostData e q d).inertia p) ∧
    (IsArithFrobAt ℤ σ P ↔
      galoisToProduct e (FrobeniusOrbits.galE e ζ a b σ) - (hostData e q d).frob p ∈ (hostData e q d).inertia p)
def DirCharInjective : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
    Function.Injective (dirChar (recMap e q d))
end Formalism.LFunctionChainParameters.LHost


