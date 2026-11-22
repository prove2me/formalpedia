-- Prove2me | Definitions.Def_UltimateL_WeaklySigma2Definable
-- name    : UltimateL_WeaklySigma2Definable
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:34:57.303357+00:00
-- url     : https://prove2.me/theorems/0ae5ac04-0cf6-4a8b-a887-f8d979a6f05f
-- title:
--   Weakly Σ₂-definable sequences and inner models (Woodin, Definitions 4.34–4.35)
-- statement:
--   For a one-variable formula $\varphi$ and an ordinal $\eta$, $(N_\varphi)^{V_\eta}=\{a\in V_\eta:V_\eta\models\varphi[a]\}$. A sequence $N=\langle N_\alpha:\alpha\in\mathrm{Ord}\rangle$ is **weakly $\Sigma_2$-definable** (Woodin's Definition 4.34) if there is a formula $\varphi(x)$ such that (1) for all $\beta<\eta_1<\eta_2<\eta_3$, if the restrictions $(N_\varphi)^{V_{\eta_1}}|\beta$ and $(N_\varphi)^{V_{\eta_3}}|\beta$ agree then all three restrictions at $\eta_1,\eta_2,\eta_3$ agree, and (2) for each $\beta$, $N|\beta$ equals $(N_\varphi)^{V_\eta}|\beta$ for all sufficiently large $\eta$. An inner model $N$ is **weakly $\Sigma_2$-definable** (Definition 4.35) when the sequence $\langle N\cap V_\alpha:\alpha\in\mathrm{Ord}\rangle$ is. This is the definability clause in the Ultimate-$L$ conjecture; $\mathrm{HOD}$ is a key example.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34, Definition 4.34 (weakly Σ₂-definable sequence) and Definition 4.35 (weakly Σ₂-definable inner model), p. 46.

import Mathlib
import Definitions.Def_UltimateL_VHierarchy
import Definitions.Def_OmegaLogic_Semantics

namespace UltimateL

universe u

open ZFSet OmegaLogic

/-- `(N_φ)^{V_η} = {a ∈ V_η : V_η ⊨ φ[a]}`, the subset of `V_η` defined by `φ` over `V_η`. -/
def nPhi (φ : setLang.Formula (Fin 1)) (η : Ordinal.{u}) : Set ZFSet.{u} :=
  {a | ∃ ha : a ∈ vLevel η,
    φ.Realize (fun _ : Fin 1 => (⟨a, ha⟩ : (vLevel η : Set ZFSet.{u})))}

/-- The level-`α` piece of the sequence determined by `(N_φ)^{V_η}`, namely
`(N_φ)^{V_η} ∩ V_α`. -/
def nPhiSeq (φ : setLang.Formula (Fin 1)) (η α : Ordinal.{u}) : Set ZFSet.{u} :=
  {a | a ∈ nPhi φ η ∧ a.rank < α}

/-- A sequence `N = ⟨N_α : α ∈ Ord⟩` is weakly `Σ₂`-definable (Woodin, Definition 4.34) if
there is a formula `φ(x)` such that (1) the restrictions to any `β` cohere across
`β < η₁ < η₂ < η₃`, and (2) for each `β`, `N|β` agrees with `(N_φ)^{V_η}|β` for all sufficiently
large `η`. -/
def IsWeaklySigma2DefinableSeq (N : Ordinal.{u} → Set ZFSet.{u}) : Prop :=
  ∃ φ : setLang.Formula (Fin 1),
    (∀ β η₁ η₂ η₃ : Ordinal.{u}, β < η₁ → η₁ < η₂ → η₂ < η₃ →
      (∀ α < β, nPhiSeq φ η₁ α = nPhiSeq φ η₃ α) →
      (∀ α < β, nPhiSeq φ η₁ α = nPhiSeq φ η₂ α ∧ nPhiSeq φ η₂ α = nPhiSeq φ η₃ α)) ∧
    (∀ β : Ordinal.{u}, ∃ η₀ : Ordinal.{u}, ∀ η ≥ η₀, ∀ α < β, N α = nPhiSeq φ η α)

/-- An inner model `N` is weakly `Σ₂`-definable (Woodin, Definition 4.35) if the sequence
`⟨N ∩ V_α : α ∈ Ord⟩` is weakly `Σ₂`-definable. -/
def IsWeaklySigma2Definable (N : Set ZFSet.{u}) : Prop :=
  IsWeaklySigma2DefinableSeq (fun α => {a | a ∈ N ∧ a.rank < α})

end UltimateL


