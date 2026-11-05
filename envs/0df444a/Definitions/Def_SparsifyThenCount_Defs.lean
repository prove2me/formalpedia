-- Prove2me | Definitions.Def_SparsifyThenCount_Defs
-- name    : SparsifyThenCount_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:30:54.271254+00:00
-- url     : https://prove2.me/theorems/6e315dd9-11eb-4427-8463-eca267e1e471
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_StepSparsify_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide
section
variable (Θ : ℕ → ℕ → ℕ → ℕ) {Idx : Type} [Enc Idx] (S : Solver Idx)
def numDG (k : ℕ) (i : Idx) (s : ℕ) (d : U × Fml) (pad : U) : ℕ :=
  bif hasNil d.2 then 0 else StepSparsify.walkSG (Θ k s) k pad (valD S k pad i d.1.length s) (rootC (d.1, SparsificationLemma.noTaut d.2))
def ADG (pick : U → U × Idx) (slU : U → U) (p : List Bool × U) : List Bool :=
  outW (fmlOf p.1, bif (planD S pick slU p.1).isNone then bruteU p
    else numDG Θ S (kcU (kU p.1) (nU p.1)) (idxU pick p.1) (precU pick slU p.1) (fmlOf p.1) p.2)
def ABDG (pick : U → U × Idx) (slU : U → U) (p : List Bool × U) : List Bool :=
  bif useMD S pick slU p.1 then AM S pick p else ADG Θ S pick slU p
end
def StRoundsDG : Prop := ∀ k K n s F : ℕ, 2 ^ restD k K n s ≤ F → 2 * 2 ^ (n / 2 ^ s + 1) ≤ F + 1
def StCorrectDG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), StepSparsify.Serves Θ Lc →
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (k n : ℕ) (φ : Sat3.CNF n),
  1 ≤ k → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eD S Q.pick slU (SatM.enc k φ) ≤ pad.length →
  ADG Θ S Q.pick slU (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
def StCorrectBDG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), StepSparsify.Serves Θ Lc →
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (k n : ℕ) (φ : Sat3.CNF n),
  1 ≤ k → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eBD S Q.pick slU (SatM.enc k φ) ≤ pad.length →
  ABDG Θ S Q.pick slU (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
def StCertDG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), StepSparsify.Serves Θ Lc →
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (pick : U → U × Idx) (slU : U → U), PolyT pick → PolyT slU → PolyT (ADG Θ S pick slU)
def StCertBDG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), StepSparsify.Serves Θ Lc →
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (pick : U → U × Idx) (slU : U → U), PolyT pick → PolyT slU →
  PolyT (ABDG Θ S pick slU) ∧ PolyT (eBD S pick slU)
def AlgDG (Θ : ℕ → ℕ → ℕ → ℕ) {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U) (rn rm : ℕ → ℝ) : Prop :=
  Alg rn rm (ABDG Θ S pick slU) (eBD S pick slU)
def StAlgSG (Θ : ℕ → ℕ → ℕ → ℕ) : Prop := StEndS fun _ _ S pick slU rn rm => AlgDG Θ S pick slU rn rm
end SparsifyThenCount


