-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:30.848989+00:00
-- url     : https://prove2.me/theorems/fede7dea-055b-4609-b997-597a523bfcbc
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_TwistedEisensteinNonvanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section Defs
variable {E K : Type} [Field E] [NumberField E] [Field K]
def RS (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ℕ) (H : (ι → E) → K) : K :=
  (((qOf P : K) ^ B)⁻¹) ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) A B), H t
def Good (P : HeightOneSpectrum (𝓞 E)) {ι : Type} (a b : ℕ) (H : (ι → E) → K) : Prop :=
  (∀ t, H t ≠ 0 → ∀ l, IntAt P ((qOf P : E) ^ a * t l)) ∧
  (∀ t δ : ι → E, (∀ l, IntAt P (δ l / (qOf P : E) ^ b)) → H (t + δ) = H t)
end Defs
section Defs2
variable {E : Type} [Field E]
def resX {n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : (Fin n → E) →ₗ[E] (Fin n → E) :=
  Matrix.toLin' (Matrix.of fun (l p : Fin n) => ρ (eN E (n + c) p.1) (Fin.castAdd c l))
def Tr {n' c' n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (t : FC n' c' n c → E) : FC n' c' n c → E :=
  fun f => (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t) (eN E (n' + c') f.1.2.1) f.1.1
end Defs2
def StabP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ((qOf P : ℕ) : K) ≠ 0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (H : (ι → E) → K), Good P a b H →
      ∀ A B : ℕ, a ≤ A → b ≤ B → RS P A B H = RS P a b H
def CoVP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ((qOf P : ℕ) : K) ≠ 0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L : (ι → E) ≃ₗ[E] (ι → E)) (τ : ι → E),
      ∃ c : K, c ≠ 0 ∧ ∀ a b : ℕ, ∃ a' b' : ℕ, ∀ H : (ι → E) → K, Good P a b H →
        Good P a' b' (fun t => H (L t + τ)) ∧ RS P a' b' (fun t => H (L t + τ)) = c * RS P a b H
def JLawP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n kj : ℕ), r = kj + c → k₀ ≤ kj → kj ≤ n → r ≤ n' + c' → k₀ ≤ n' →
    ∀ κ ∈ JQ P (qOf P) kj n c, ∃ lam : K, lam ≠ 0 ∧ ∀ y : HomE E (n' + c') (n + c),
      PhiQ (qOf P) ξ k₀ r c' n' c n (κ.symm.toLinearMap ∘ₗ y) = lam * PhiQ (qOf P) ξ k₀ r c' n' c n y
def MuNeP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), cq ≠ 0 → ∀ a : E, a ≠ 0 → locChar (qOf P) cq χ a ≠ 0
def OmStepP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (sq cq : K), sq ≠ 0 → cq ≠ 0 →
    ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n kj : ℕ), r = kj + c → k₀ ≤ kj → kj ≤ n → r ≤ n' + c' → k₀ ≤ n' →
    ∀ (g₀ : (Fin (n' + c') → E) ≃ₗ[E] (Fin (n' + c') → E)) (h ρ κ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)),
      κ ∈ JQ P (qOf P) kj n c → ∃ C : K, C ≠ 0 ∧ ∀ x : HomE E (n' + c') (n + c),
        om (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq g₀ (ρ * h * κ) (PhiQ (qOf P) ξ k₀ r c' n' c n) x =
          C * om (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq g₀ h (PhiQ (qOf P) ξ k₀ r c' n' c n)
            ((ρ⁻¹).toLinearMap ∘ₗ x)
def PhiSuppP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n → k₀ ≤ n' →
    ∀ y : HomE E (n' + c') (n + c), PhiQ q ξ k₀ r c' n' c n y ≠ 0 →
      ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (y (eN E (n' + c') s) l)
def PhiPerP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (y ε : HomE E (n' + c') (n + c)),
      (∀ (s : ℕ) (l : Fin (n + c)), IntAt P (ε (eN E (n' + c') s) l / (qOf P : E))) →
      PhiQ (qOf P) ξ k₀ r c' n' c n (y + ε) = PhiQ (qOf P) ξ k₀ r c' n' c n y
def BddEntP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (R : Ranks) (j : ℕ)
    (h : AutYL E R j), BddL R P j h →
      (∀ (s : ℕ) (l : Fin (R.N j + cOf R j)), IntAt P ((qOf P : E) ^ j * h (eN E _ s) l)) ∧
      (∀ (s : ℕ) (l : Fin (R.N j + cOf R j)), IntAt P (h.symm (eN E _ s) l))
def GSuppP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime →
    ∀ (a b : ℕ) (mu : E → K) (v : E → ℤ) (sq : K) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (h : (Fin b → E) ≃ₗ[E] (Fin b → E)) (Φ : SF E K a b) (j : ℕ),
    (∀ y, Φ y ≠ 0 → ∀ (s : ℕ) (l : Fin b), IntAt P (y (eN E a s) l)) →
    (∀ (s : ℕ) (l : Fin a), IntAt P (g₀.symm (eN E a s) l)) →
    (∀ (s : ℕ) (l : Fin b), IntAt P ((qOf P : E) ^ j * h (eN E b s) l)) →
    ∀ x, om mu v sq g₀ h Φ x ≠ 0 → ∀ (s : ℕ) (l : Fin b), IntAt P ((qOf P : E) ^ j * x (eN E a s) l)
def GPerP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime →
    ∀ (a b : ℕ) (mu : E → K) (v : E → ℤ) (sq : K) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (h : (Fin b → E) ≃ₗ[E] (Fin b → E)) (Φ : SF E K a b) (e : ℕ),
    (∀ y ε : (Fin a → E) →ₗ[E] (Fin b → E),
      (∀ (s : ℕ) (l : Fin b), IntAt P (ε (eN E a s) l / (qOf P : E))) → Φ (y + ε) = Φ y) →
    (∀ (s : ℕ) (l : Fin a), IntAt P ((qOf P : E) ^ e * g₀ (eN E a s) l)) →
    (∀ (s : ℕ) (l : Fin b), IntAt P (h.symm (eN E b s) l)) →
    ∀ x δ : (Fin a → E) →ₗ[E] (Fin b → E),
      (∀ (s : ℕ) (l : Fin b), IntAt P (δ (eN E a s) l / (qOf P : E) ^ (e + 1))) →
      om mu v sq g₀ h Φ (x + δ) = om mu v sq g₀ h Φ x
def HGoodP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime →
    ∀ (n' c' n c D j : ℕ), j ≤ D → ∀ psi : E → K, PsiOk D P psi →
    ∀ G : SF E K (n' + c') (n + c),
    (∀ x, G x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l)) →
    (∀ x δ : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E),
      (∀ (s : ℕ) (l : Fin (n + c)), IntAt P (δ (eN E (n' + c') s) l / (qOf P : E) ^ j)) → G (x + δ) = G x) →
    ∀ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      Good P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t)))
def ChArgBddP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c j : ℕ)
    (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)),
    (∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l)) →
      IntAt P ((qOf P : E) ^ j * chArg (n := n) (c := c) x)
def XXP : Prop :=
  ∀ (E : Type) [Field E] (n' c' n c : ℕ) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ρ ∈ R1 E n c →
    ∀ (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E),
      ρ.toLinearMap ∘ₗ xx1 xj t = xx1 (resX ρ ∘ₗ xj) (Tr ρ t)
def TrAffP : Prop :=
  ∀ (E : Type) [Field E] (n' c' n c : ℕ) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ρ ∈ R1 E n c →
    ∃ L : (FC n' c' n c → E) ≃ₗ[E] (FC n' c' n c → E), ∀ t, Tr ρ t = L t + Tr ρ 0
def ResXSurjP : Prop :=
  ∀ (E : Type) [Field E] (n' n c : ℕ) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ρ ∈ R1 E n c →
    ∀ y : (Fin n' → E) →ₗ[E] (Fin n → E), ∃ xj, resX ρ ∘ₗ xj = y
def ChArgP : Prop :=
  ∀ (E : Type) [Field E] (n' c' n c : ℕ) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ρ ∈ R1 E n c →
    ∀ (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E),
      chArg (ρ.toLinearMap ∘ₗ xx1 xj t) = chArg (xx1 xj t) +
        chArg (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (0 : FC n' c' n c → E))
end PI.TwistedEisensteinNonvanishing.W


