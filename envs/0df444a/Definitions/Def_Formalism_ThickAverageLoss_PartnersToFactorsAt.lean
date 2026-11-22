-- Prove2me | Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
-- name    : Formalism_ThickAverageLoss_PartnersToFactorsAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:38:00.873948+00:00
-- url     : https://prove2.me/theorems/a3529633-8bae-49ca-965f-aa40a3ca1203
-- title:
--   Partners To Factors At
-- statement:
--   Definitions and structural lemmas for Partners To Factors At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/PartnersToFactorsAt.lean

import Definitions.Def_Formalism_ThickAverageLoss_Statement
import Definitions.Def_Formalism_CorankShare_StatementFR
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
abbrev E0 := ZMod 2 × ZMod 2
def sgn2 (e : ZMod 2) : ℝ := if e = 0 then 1 else -1
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def InPhi (g : E0 × H) : Prop := g.1.1 = 0
instance : DecidablePred (InPhi (H := H)) := fun g => inferInstanceAs (Decidable (g.1.1 = 0))
def cconj : E0 × H := ((1, 1), 0)
def topPl (t : H) : E0 × H := ((0, 0), t)
def thickPl (t : H) : E0 × H := ((0, 1), t)
def PhiSet : Finset (E0 × H) := univ.filter InPhi
end
structure CycHost (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] where
  cv : AddChar (E0 × H) ℂ → ℕ → ℂ
  cv_zero : ∀ n, cv 0 n = 1
  ell : AddChar (E0 × H) ℂ → ℂ
  chC : AddChar (E0 × H) ℂ
  psC : AddChar (E0 × H) ℂ
  chpsC : AddChar (E0 × H) ℂ
  chC_apply : ∀ g, chC g = (sgn2 g.1.1 : ℂ)
  psC_apply : ∀ g, psC g = (sgn2 g.1.2 : ℂ)
  chpsC_apply : ∀ g, chpsC g = ((sgn2 g.1.1 * sgn2 g.1.2 : ℝ) : ℂ)
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def GC (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) (y : ℝ) : ℂ :=
  if ψ = 0 then ((Gz y : ℝ) : ℂ) else
    (∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * Hs.ell ψ
def vonMangoldtClassSum (Hs : CycHost H) (g : E0 × H) (a w : ℝ) : ℝ :=
  ((1 / (Fintype.card (E0 × H) : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ,
    ψ (-g) * ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w : ℝ) : ℂ)).re
def askTop (Hs : CycHost H) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ :=
  ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), 2 * vonMangoldtClassSum Hs g a (w (cconj + g + topPl t))
def ledTop (Hs : CycHost H) (a : ℝ) (w : E0 × H → ℝ) : ℝ :=
  a * (Real.log a - 1 - Real.eulerMascheroniConstant + (Hs.ell Hs.chC).re
    - (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ))
def balTop (Hs : CycHost H) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ :=
  ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)),
    ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((w (cconj + g + topPl t) : ℝ) : ℂ)
      * GC Hs ψ (a / w (cconj + g + topPl t))).re
def Balance : Prop :=
  ∀ (Hs : CycHost H) (a : ℝ) (t : H) (w : E0 × H → ℝ), 0 < a → (∀ ρ, 0 < w ρ) →
    askTop Hs a t w - ledTop Hs a w = balTop Hs a t w
end
structure Nodes (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (m : ℕ) where
  T : Finset H
  T2 : Finset H
  a : H → ℝ
  bj : Fin m → ℝ
  w : H → Fin m → E0 × H → ℝ

  w_thick : ∀ u0 j t, t ∈ T2 → w u0 j (thickPl (t + u0)) = bj j
  w_pos : ∀ u0 j ρ, 0 < w u0 j ρ
  a_pos : ∀ t, 0 < a t
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def asked {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (u0 : H) : ℝ :=
  ∑ t ∈ Nd.T, ∑ j : Fin m, askTop Hs (Nd.a t) t (Nd.w u0 j)
def sizeData₂ {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (u0 : H) : ℝ :=
  ∑ t ∈ Nd.T, ∑ j : Fin m, ledTop Hs (Nd.a t) (Nd.w u0 j)
def signal {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) : ℝ :=
  ((Nd.T2.card : ℝ) / Fintype.card H) / 2 * ∑ t ∈ Nd.T, ∑ j : Fin m, Nd.bj j *
    (GC Hs 0 (Nd.a t / Nd.bj j) + GC Hs Hs.psC (Nd.a t / Nd.bj j) - GC Hs Hs.chC (Nd.a t / Nd.bj j)
      - GC Hs Hs.chpsC (Nd.a t / Nd.bj j)).re
def IsThickAt (T2 : Finset H) (u0 : H) (ρ : E0 × H) : Prop := ρ ∈ T2.image (fun t => thickPl (t + u0))
instance (T2 : Finset H) (u0 : H) : DecidablePred (IsThickAt T2 u0) :=
  fun ρ => inferInstanceAs (Decidable (ρ ∈ T2.image (fun t => thickPl (t + u0))))
def restAvg {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) : ℝ :=
  (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ Nd.T, ∑ j : Fin m,
    ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt Nd.T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((Nd.w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC Hs ψ (Nd.a t / Nd.w u0 j (cconj + g + topPl t))).re
def ThickAverage : Prop :=
  ∀ {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m),
    (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ Nd.T, ∑ j : Fin m, balTop Hs (Nd.a t) t (Nd.w u0 j)
      = signal Hs Nd + restAvg Hs Nd
end
def SpreadRepair : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (d : ℕ) (e : Fin d → ℕ) (τ : ℕ),
    ({v : Fin d → R | ∀ i, ϖ ^ e i ∣ v i} ∩ {v : Fin d → R | ∀ i, ϖ ^ τ ∣ v i})
        = {v : Fin d → R | ∀ i, ϖ ^ max (e i) τ ∣ v i} ∧
    (∑ i, max (e i) τ = d * τ + ∑ i, (e i - τ)) ∧
    ∀ (β S V g : ℕ), ((univ.filter (fun i => τ + β * S < e i)).card ≤ g) → (∀ i, e i ≤ V * S) →
      ∑ i, (e i - τ) ≤ d * (β * S) + g * (V * S)
structure PartnersToFactorsAt (C ε x : ℝ) (P : SizeParameters) {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (Hs : CycHost H) (Nd : Nodes H P.m) (u0 : H) where
  ι : Type
  fι : Fintype ι
  ω : ι → ℝ
  ω_nonneg : ∀ i, 0 ≤ ω i
  ω_sum : (∑ i, ω i) = 1

  D : ℕ
  D_pos : 0 < D
  slope : Fin D → ℝ

  muM : ι → ℝ
  muMax : ι → ℝ
  topS : ι → ℝ
  lowS : ι → ℝ
  ix : ι → ℝ
  tau : ι → ℝ
  lev : ι → ℝ
  hB : ι → ℝ
  logT : ι → ℝ
  muNmax : ι → ℝ

  uMin : ℝ
  uF : ℝ
  HH : ℝ
  eta : ℝ
  e : ℝ
  Ll : ℝ
  uMin_pos : 0 < uMin
  HH_nonneg : 0 ≤ HH
  eta_nonneg : 0 ≤ eta
  e_nonneg : 0 ≤ e
  Ll_nonneg : 0 ≤ Ll

  EM : ℝ
  Ediv : ℝ
  Elow : ℝ
  Eserv : ℝ
  Ephic : ℝ
  Eram : ℝ
  Ekap : ℝ
  firstMomentError : ℝ
  Enet : ℝ
  Eh : ℝ
  Esize : ℝ
  Elev : ℝ
  Ecnt : ℝ
  lowC : ℝ

  GGlog : ℝ
  Egg : ℝ
  ElevTh : ℝ
  Emax : ℝ
  Emax_nonneg : 0 ≤ Emax

  bottomSize_nonneg : 0 ≤ P.b1
  logOm : ℝ
  logv : ℝ

  fr_low : ∀ j, (∑ i, ω i * (muM i + topS i + lowS i - ix i - lev i - hB i)) - HH ≤ slope j
  fr_share : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
    ((univ.filter (fun j => slope j < (∑ i, ω i * (muM i + topS i + lowS i - ix i - lev i - hB i)) - τ - Ll)).card : ℝ)
      ≤ (2 * eta + 4 * (uF / (uF + τ)) + 4 * Real.sqrt e) * D

  u_ge_min : uMin ≤ uF
  u_ge_spread : ∀ i, muNmax i - hB i - (∑ i, ω i * (muM i + topS i + lowS i - ix i - lev i - hB i)) ≤ uF
  u_least : uF = uMin ∨ ∃ i, uF = muNmax i - hB i - (∑ i, ω i * (muM i + topS i + lowS i - ix i - lev i - hB i))

  div : (∑ j, slope j) / D ≤ lowC + Ediv
  low_match : lowC - Elow ≤ ∑ i, ω i * lowS i

  gains : asked Hs Nd u0 - (Eserv + Ephic + Eram + Egg) - (P.m : ℝ) * (∑ t ∈ Nd.T, Nd.a t) * GGlog
    ≤ ∑ i, ω i * (topS i - tau i)

  rep_max : ∀ i, muNmax i ≤ muMax i + topS i + lowS i - tau i + Emax
  rep_ix : ∀ i, ix i ≤ tau i + Ekap

  var_M : ∀ i i', muMax i - muM i' ≤ firstMomentError

  muM_le : ∀ i, muM i ≤ muMax i
  var_net : ∀ i i', (topS i + lowS i - tau i) - (topS i' + lowS i' - tau i') ≤ Enet
  var_h : ∀ i i', hB i' - hB i ≤ Eh

  size : ∀ i, hB i ≤ (∑ t ∈ Nd.T, ∑ _j : Fin P.m, (Nd.a t * Real.log (Nd.a t) - Nd.a t - Nd.a t * logOm))
    - (∑ t ∈ Nd.T, Nd.a t * logT i) + Esize
  muM_low : ∀ i, -EM ≤ muM i
  level : ∀ i, lev i ≤ (∑ t ∈ Nd.T, (P.m : ℝ) * (Nd.a t / P.k + P.b1) * logT i) + ElevTh + Elev
  count_lo : ∀ i, ((∑ j : Fin P.m, (1 / ((PhiSet (H := H)).card : ℝ)) *
    ∑ ρ ∈ PhiSet (H := H), (Real.log (Nd.w u0 j ρ) + logv - Real.log Real.pi)) + (P.m : ℝ) * GGlog) - Ecnt ≤ logT i

  count_hi : ∀ i, logT i ≤ C * P.m * P.Lrd
  period : logOm = Real.eulerMascheroniConstant + Real.log Real.pi - logv - (Hs.ell Hs.chC).re
end Formalism.D5


