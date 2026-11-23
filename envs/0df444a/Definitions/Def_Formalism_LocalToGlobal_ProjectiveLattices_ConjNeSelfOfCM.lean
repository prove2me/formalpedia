-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ConjNeSelfOfCM
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ConjNeSelfOfCM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:58.844796+00:00
-- url     : https://prove2.me/theorems/981c2bd0-bdae-4ae1-98c6-4daf09cffda2
-- title:
--   Conj Ne Self Of CM
-- statement:
--   Definitions and structural lemmas for Conj Ne Self Of CM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ConjNeSelfOfCM.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} [StarRing (𝓞 E)]
def SatDir (T : CDVR) {d : ℕ} (uvec : Lt1 Dw → Fin d → T.Fr) : Prop :=
  ∀ τ : E →+* ℂ, ∃ W : Fin (Dw.mult τ) → Fin d → T.V,
    ∀ i i' : Fin (Dw.mult τ), ∑ j, uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (W i j) = if i' = i then 1 else 0
variable (Dw) in

def DomW (a : (E →+* ℂ) × ℕ → ℕ) : Prop := Crude.Dom Dw.mult (fun τ i => a (τ, i))
def crudeBd {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (D : ℕ) : ℝ :=
  (ramOverZ la : ℝ) * (D : ℝ) / ((resCharOf la : ℝ) - 1)
omit [IsCMField E] [StarRing (𝓞 E)] in
variable (Dw) in

def colP {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) : Lt1 Dw → Fin n :=
  fun p => Fin.castLE hn (Fintype.equivFin (Lt1 Dw) p)
open Classical in
variable (Dw) in

def P1 (T : CDVR) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) :
    MvPolynomial (LtN Dw n) T.Fr :=
  MvPolynomial.map (Int.castRingHom T.Fr) (Crude.Pmin Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))
open Classical in
variable (Dw) in

def fact1 (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) : ℕ :=
  (Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i))).prod fun _ t => t.factorial
def crudeInf {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d) (w0 : O)
    (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (e : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  ⨅ (P : MvPolynomial (LtN Dw n) T.Fr) (_ : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n d) (_ : IsIntPS T f),
    nval T.V e (nabValN B T.Fr h w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => uvec ⟨ℓ.1, ℓ.2.1⟩) P)
end Gen
end Formalism.L2.Pj


