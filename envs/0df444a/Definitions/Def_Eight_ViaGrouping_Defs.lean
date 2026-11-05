-- Prove2me | Definitions.Def_Eight_ViaGrouping_Defs
-- name    : Eight_ViaGrouping_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:47:43.980712+00:00
-- url     : https://prove2.me/theorems/48c3e051-1df7-4880-a209-cd743892573c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_Eight_Level_Defs
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
structure GiveP {C : Type} (Np : Procs C) (c : C) {g : ℕ} (N : Net g) (P τ S : ℕ) : Prop where
  P_eq : Np.P c = P
  len_eq : ∀ a : Fin g, Np.len c a = N.len a
  cap_eq : ∀ a b : Fin g, a ≠ b → Np.cap c a b = N.c a b
  mem_runs : ∀ (a : Fin g) (z : List Bool), z.length = N.len a → Np.mem.Runs (c, (a.val, z)) τ S (decide (z ∈ N.S a))
  W_runs : ∀ (a : Fin g), ∀ z ∈ N.S a, Np.W.Runs (c, (a.val, z)) τ S (N.W a z)
  Ψ_runs : ∀ (a b : Fin g), a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Np.Ψ.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')
  f_runs : ∀ (a b : Fin g), a ≠ b → ∀ z ∈ N.S a, ∀ θ ∈ words (N.c a b), Np.f.Runs (c, ((a.val, b.val), (z, θ))) τ S (N.f a b z θ)
structure IsNetworkP {C : Type} {g : ℕ} (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ) : Prop where
  is : N.Is P B
  τ_pos : 1 ≤ τ
  given : GiveP Np c N P τ S
def Correct (NA : NetAlg) (g K : ℕ) (ε b : ℝ) : Prop := ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∃ T : ℕ, (NA.app Np).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * τ
structure KeepsP {C : Type} [Enc C] (Np : Procs C) : Prop where
  keeps : Np.Keeps
  P : Unary Np.P
def AlgKeeps (NA : NetAlg) : Prop :=
  ∀ (C : Type) [HasSize C] [Enc C] [Carried C] (Np : Procs C), KeepsP Np → Nonempty (IsPolyT (NA.app Np))
section Program
variable {C : Type} [HasSize C] (K g : ℕ) (Np : Procs C)
def lamP (cx : C × ℕ) : ℕ := Colouring.beta K g (Uc g Np.toPaperNetwork cx.1) (Np.P cx.1)
def goodP (cx : C × ℕ) : Bool :=
  ((List.range K).all fun G => decide (K * (members K g cx.2 G).length ≤ 2 * g)) &&
  (List.range K).all fun G => (List.range K).all fun G' =>
    G == G' || decide (K ^ 3 * lbLen K g Np.toPaperNetwork cx.1 cx.2 G G' ≤ K * Uc g Np.toPaperNetwork cx.1 + g * Np.P cx.1)
def qMb (u : (X0 C × ℕ) × ℕ) : C × WQ := (u.1.1.1.1, (u.2 % g, zA K g Np.toPaperNetwork u.1 (u.2 % g)))
def qPsi (u : (X0 C × ℕ) × ℕ) : C × PsiQ :=
  (u.1.1.1.1, ((u.2 / g, u.2 % g), (zA K g Np.toPaperNetwork u.1 (u.2 / g), zA K g Np.toPaperNetwork u.1 (u.2 % g))))
def wM : Stepped ((X0 C × ℕ) × ℕ) ℤ := gated (mapIn (qW K g Np.toPaperNetwork) Np.mem) (mapIn (qW K g Np.toPaperNetwork) Np.W)
def psiP : Stepped ((X0 C × ℕ) × ℕ) ℤ :=
  gated (mapIn (qW K g Np.toPaperNetwork) Np.mem) (gated (mapIn (qMb K g Np) Np.mem) (mapIn (qPsi K g Np) Np.Ψ))
def fM : Stepped ((X0 C × ℕ) × ℕ) ℤ := gated (mapIn (qW K g Np.toPaperNetwork) Np.mem) (mapIn (qF K g Np.toPaperNetwork) Np.f)
def termP : Stepped ((X0 C × ℕ) × ℕ) ℤ :=
  ite (isOne K g) (const 1) (ite (isW g) (wM K g Np) (ite (isPsi K g) (psiP K g Np) (fM K g Np)))
def tableM : Stepped (X0 C) ℤ :=
  ite (validB K g Np.toPaperNetwork) (sumRange (nStates K g Np.toPaperNetwork) (prodRange (nPairs g) (termP K g Np))) (const 0)
def searchP : Stepped C (Option ℕ) := firstRange (nCol K g) (ofFun (goodP K g Np)) id
end Program
def netAlg (K g : ℕ) (E : Paper.CliqueAlgorithm) : NetAlg :=
  ⟨fun Np => optBind (searchP K g Np) (E.app (lamP K g Np) (tableM K g Np)) zeroOf⟩
def StSearch : Prop := ∀ (K : ℕ) (hK : 2 ≤ K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net (3 * K ^ 8)) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∃ x < K ^ (3 * K ^ 8), (List.range (K ^ (3 * K ^ 8))).find? (fun x => goodP K (3 * K ^ 8) Np (c, x)) = some x ∧
    Good N.c P (Paper.grouping (g := 3 * K ^ 8) (by omega : 0 < K) x)
def StTable : Prop := ∀ K g : ℕ, ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (hK0 : 0 < K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ServesInst (tableM K g Np) (c, x) L (P * (2 * g / K) + g ^ 2 * B) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (S + c₁ * (size c + P + B) ^ c₁)
      (Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L)
def StValue : Prop := ∀ (K g : ℕ) (hK0 : 0 < K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x L : ℕ, (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) → Paper.cliqueValue L (Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L) = N.value
def StKeeps : Prop := ∀ (K g : ℕ) (E : Paper.CliqueAlgorithm), E.PolyTimeSteps → AlgKeeps (netAlg K g E)
def StLemGrouping : Prop := ∀ (K : ℕ) (e : ℝ) (E : Paper.CliqueAlgorithm), 2 ≤ K → 0 ≤ e → E.Within K e → Correct (netAlg K (3 * K ^ 8) E) (3 * K ^ 8) K e (e + 2)
def ofNetwork {g : ℕ} (N : Paper.Network (Fin g) (List Bool) (List Bool)) (n : Fin g → ℕ) : Net g where
  len := n
  S := N.S
  W := N.W
  Ψ := N.Ψ
  c := N.c
  f := N.f
def ofProcs {C : Type} [HasSize C] (Np : Paper.NetworkProcedures C) (Pf : C → ℕ) (Q : Stepped (C × PsiQ) ℤ) : Procs C where
  P := Pf
  B := fun _ => 0
  len := Np.n
  cap := Np.cap
  mem := mapIn (fun _ => ()) (const true)
  W := Np.W
  Ψ := Q
  f := Np.f
def StBridge : Prop := ∀ (C : Type) [HasSize C] (g : ℕ) (Np : Paper.NetworkProcedures C) (Pf : C → ℕ) (Q : Stepped (C × PsiQ) ℤ) (c : C) (N : Paper.Network (Fin g) (List Bool) (List Bool)) (P B τ S : ℕ),
  1 ≤ P → 1 ≤ τ → Paper.IsNetwork Np c N P B τ S → Pf c = P →
  (∀ a b : Fin g, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Q.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')) →
  IsNetworkP (ofProcs Np Pf Q) c (ofNetwork N fun a => Np.n c a) P (B + 1) τ (S + 2) ∧ (ofNetwork N fun a => Np.n c a).value = N.value ∧ (ofNetwork N fun a => Np.n c a).U = N.U
end Eight.ViaGrouping


