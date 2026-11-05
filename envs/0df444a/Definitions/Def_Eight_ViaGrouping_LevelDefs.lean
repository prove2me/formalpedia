-- Prove2me | Definitions.Def_Eight_ViaGrouping_LevelDefs
-- name    : Eight_ViaGrouping_LevelDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:49:58.742413+00:00
-- url     : https://prove2.me/theorems/73c45ec1-2bdf-4bf0-9f25-c4d6d59402e4
-- title:
--   Level Defs
-- statement:
--   Definitions and structural lemmas for Level Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Eight.SecNetworks Eight.Level
def levelProcs {C : Type} [HasSize C] (g : ℕ) (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ) (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) : Procs (C × ℕ) :=
  ofProcs (levelNet g tr lam R) (fun c => g ^ 3 * lam c.1) (ofFun fun x => psi (lam x.1.1) x.1.2 x.2)
noncomputable def levelNetP (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : Net (nParts g g tr) :=
  ofNetwork (netOfι g tr lam y Rm) fun _ => g ^ 3 * lam
def levelAlgP (g : ℕ) (psiR psiC : ℕ → ℕ → PsiQ → ℤ) (NA : NetAlg) : Evaluator :=
  ⟨fun lam R => bind (sumRange (numPat8 g lam) (Stepped.ite (useRowP g lam) (NA.app (levelProcs g false psiR lam R)) (NA.app (levelProcs g true psiC lam R))))
    (ofFun fun p => p.2 / ((2 ^ (tOf (lam p.1) * nRect g) : ℕ) : ℤ))⟩
def StPsiOK (g : ℕ) (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ) : Prop :=
  ∀ (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)), 1 ≤ lam → y < (tOf lam + 1) ^ nRect g → ∀ a b : Fin (nParts g g tr), a ≠ b →
    ∀ z ∈ (netOfι g tr lam y Rm).S a, ∀ z' ∈ (netOfι g tr lam y Rm).S b, psi lam y ((a.val, b.val), (z, z')) = (netOfι g tr lam y Rm).Ψ a b z z'
def StPsiPoly (psi : ℕ → ℕ → PsiQ → ℤ) : Prop :=
  ∀ (C : Type) [Enc C] (lam : C → ℕ), Unary lam → PolyT fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2
def StOfPaperNetwork : Prop := ∀ (NA : NetAlg) (g K : ℕ) (ε b : ℝ), Correct NA g K ε b →
  ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : PNet C) (Pf : C → ℕ) (Q : Stepped (C × PsiQ) ℤ) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B t S : ℕ),
    1 ≤ P → 1 ≤ t → Np.Presents c N t S → N.Sized P B → Pf c = P →
    (∀ a b : Fin g, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Q.Runs (c, ((a.val, b.val), (z, z'))) t S (N.Ψ a b z z')) →
    ∃ T : ℕ, (NA.app (ofProcs Np Pf Q)).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧
      (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * t
def StLevelP : Prop := ∀ (K g : ℕ) (e : ℝ) (psiR psiC : ℕ → ℕ → PsiQ → ℤ) (NA : NetAlg), 2 ≤ K → K ≤ g → 0 ≤ e → StPsiOK g false psiR → StPsiOK g true psiC →
  Correct NA g K e (e + 2) → (levelAlgP g psiR psiC NA).Correct (g * g) ((rho + 2 / K) * e + 2 / K)
def StLevelKeepsP : Prop := ∀ (g : ℕ) (psiR psiC : ℕ → ℕ → PsiQ → ℤ) (NA : NetAlg), StPsiPoly psiR → StPsiPoly psiC → AlgKeeps NA → (levelAlgP g psiR psiC NA).Keeps
end Eight.ViaGrouping


