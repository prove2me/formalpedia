-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_GroupAnalysis
-- name    : EntAssistOneWay_Separation_GroupAnalysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:10.18606+00:00
-- url     : https://prove2.me/theorems/7e14d0e1-a4ab-418b-b25f-025d1987f83f
-- title:
--   The central-phase operators and shifted correlations
-- statement:
--   In the standard basis of $\mathbb C^{G\times G}$ set
--   $$K=|G|^{-1}\sum_{u,v,w}|u,v\rangle\langle uw,vw^{-1}|,\qquad P=\tfrac13\sum_{u,v}\sum_{j\in\mathbb F_3}|u,v\rangle\langle\zeta^ju,\zeta^jv|.$$
--   For functions $w_s:G^S\to\mathbb C$ and arrays $g_1,g_2$, define
--   $$\operatorname{Corr}(g_1,g_2)=\prod_s w_s(g_1\operatorname{shift}_s(g_2)),\quad\operatorname{Corr}_{\rm ind}(g_1,g_2,\phi)=\prod_s w_s(\zeta^{\phi_s}g_1\operatorname{shift}_s(g_2)).$$
--   For matrix-valued maps $O_s$, set $T(g_1,g_2)=\mathbb E_s O_s(g_1\operatorname{shift}_s(g_2))$.
--
--   The entries of $K$ and $P$ are the literal coefficients of the displayed operators, and their norms elsewhere are Euclidean spectral norms. These objects fix the conventions for the analytic milestones.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), pp. 27–28, Theorem 5.4 and operators K, P; p. 33, Theorem 5.8

import Definitions.Def_EntAssistOneWay_Separation_GroupProblems

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- K from p. 28, in the standard basis labelled by G × G. -/
def mixingK (G : Type) [Group G] [Fintype G] : Matrix (G × G) (G × G) ℂ :=
  fun a b => (Fintype.card G : ℂ)⁻¹ *
    ∑ w : G, if b = (a.1 * w, a.2 * w⁻¹) then 1 else 0

/-- P from p. 28: average of the three simultaneous central rotations. -/
def phaseP {G : Type} [Group G] (ζ : G) : Matrix (G × G) (G × G) ℂ :=
  fun a b => (3 : ℂ)⁻¹ * ∑ j : ZMod 3,
    if b = (ζ ^ j.val * a.1, ζ ^ j.val * a.2) then 1 else 0

def correlation {G : Type} [Group G] {r : ℕ}
    (w : ShiftSpace r → (ShiftSpace r → G) → ℂ)
    (g₁ g₂ : ShiftSpace r → G) : ℂ :=
  ∏ s, w s (shiftedProduct g₁ g₂ s)

def independentCorrelation {G : Type} [Group G] {r : ℕ}
    (ζ : G) (w : ShiftSpace r → (ShiftSpace r → G) → ℂ)
    (g₁ g₂ : ShiftSpace r → G) (φ : ShiftSpace r → ZMod 3) : ℂ :=
  ∏ s, w s (phaseArray ζ (φ s) (shiftedProduct g₁ g₂ s))

/-- T of Theorem 5.8, as a finite uniform average of matrices. -/
def momentOperator {G : Type} [Group G] {r d : ℕ}
    (O : ShiftSpace r → (ShiftSpace r → G) → Matrix (Fin d) (Fin d) ℂ)
    (g₁ g₂ : ShiftSpace r → G) : Matrix (Fin d) (Fin d) ℂ :=
  uniformAverage (fun s => O s (shiftedProduct g₁ g₂ s))

end

end EntAssistOneWay.Separation


