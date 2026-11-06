-- Prove2me | Definitions.Def_SplitSat_Defs
-- name    : SplitSat_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:21:40.60426+00:00
-- url     : https://prove2.me/theorems/d14e2fa6-8dba-4df7-bbb9-a0e608112cfc
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_Eight_Cor_WidthProg
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_ThreeSatPrinted_Defs
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_WidthK_Top_Sat
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.snd


set_option autoImplicit false
section
section
namespace SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight Eight.ViaGrouping Eight.Width
def DecidesW (w : ℕ) (D : StepMachine (List Unit × Fml) Bool) (δ : ℝ) (c : ℕ) : Prop := ∀ (N : ℕ) (ψ : Fml),
  (∀ C ∈ ψ, C.length ≤ w ∧ ∀ l ∈ C, l.1 < N) → ψ.Nodup →
  ∃ (T : ℕ) (b : Bool), D.Runs (List.replicate N (), ψ) T (c * (N + 2) ^ c) b ∧ (b = true ↔ ψ.Sat) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * N)
abbrev Decides3 (D : StepMachine (List Unit × Fml) Bool) (δ : ℝ) (c : ℕ) : Prop := DecidesW 3 D δ c
def Simulates (M : Turing.TM2ComputableAux Bool Bool) (Ms : StepMachine (List Bool) Bool) (q : ℕ) : Prop :=
  ∀ (x : List Bool) (b : Bool) (T S : ℕ), Ms.Runs x T S b →
    Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) (q * (T + 1) * (x.length + S + 1) ^ q))
abbrev NFml : Type := List Unit × Fml
def stepN (step : Fml → Option (Fml × Fml)) (x : NFml) : Option (NFml × NFml) := (step x.2).map fun lh => ((x.1, lh.1), (x.1, lh.2))
def reduceCore (step : Fml → Option (Fml × Fml)) (D : StepMachine (List Unit × Fml) Bool) : StepMachine (List Unit × Fml) Bool :=
  Stepped.ite (fun p => hasNil p.2) (Stepped.const false) (Stepped.walk (stepN step) (fun p : List Unit × Fml => ((p.1, rootP p.2) : NFml)) (Stepped.mapIn widthP D))
def REDUCE (k τ : ℕ) (D : StepMachine (List Unit × Fml) Bool) : StepMachine (List Bool) Bool := Stepped.mapIn (decU k) (reduceCore (stepK (thetaU τ) k) D)
def StLeaf : Prop := ∀ (k B n : ℕ) (x : Fml), (∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → x.length ≤ B * n →
  (∀ C ∈ (widthP (List.replicate n (), x)).2, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < (widthP (List.replicate n (), x)).1.length) ∧ (widthP (List.replicate n (), x)).2.Nodup ∧
  (widthP (List.replicate n (), x)).1.length ≤ (1 + (k - 3) * B) * n ∧ ((widthP (List.replicate n (), x)).2.Sat ↔ x.Sat)
def StSparsifyK : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ τ Dd B Sk : ℕ, Sparsifies k ε (stepK (thetaU τ) k) rootP Dd B Sk
def StReduceCore : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ τ Dd B Sk : ℕ, Sparsifies k (δ / 3) (stepK (thetaU τ) k) rootP Dd B Sk →
  ∀ (D : StepMachine (List Unit × Fml) Bool) (δ₃ : ℝ) (c : ℕ), 0 ≤ δ₃ → δ₃ * (1 + ((k : ℝ) - 3) * B) ≤ δ / 3 → Decides3 D δ₃ c → ∃ c' : ℕ, DecidesW k (reduceCore (stepK (thetaU τ) k) D) δ c'
def StReduce : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ τ Dd B Sk : ℕ, Sparsifies k (δ / 3) (stepK (thetaU τ) k) rootP Dd B Sk →
  ∀ (D : StepMachine (List Unit × Fml) Bool) (δ₃ : ℝ) (c : ℕ), 0 ≤ δ₃ → δ₃ * (1 + ((k : ℝ) - 3) * B) ≤ δ / 3 → Decides3 D δ₃ c → ∃ c' : ℕ, Decides (REDUCE k τ D) k δ c'
def StReduceCert : Prop := ∀ (k τ : ℕ) (D : StepMachine (List Unit × Fml) Bool), PolyTimeSteps D → PolyTimeSteps (REDUCE k τ D)
def Sat3SubexpBy (Ds : ℝ → StepMachine (List Unit × Fml) Bool) : Prop := ∀ δ₃ : ℝ, 0 < δ₃ → PolyTimeSteps (Ds δ₃) ∧ ∃ c : ℕ, Decides3 (Ds δ₃) δ₃ c
def StImplication : Prop := ∀ Ds : ℝ → StepMachine (List Unit × Fml) Bool, Sat3SubexpBy Ds → ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ →
  ∃ (τ : ℕ) (δ₃ : ℝ), 0 < δ₃ ∧ PolyTimeSteps (REDUCE k τ (Ds δ₃)) ∧ ∃ c' : ℕ, Decides (REDUCE k τ (Ds δ₃)) k δ c'
def core3 (ℓ τ : ℕ) : StepMachine (List Unit × Fml) Bool :=
  Stepped.mapIn Prod.snd (Stepped.ite hasNil (Stepped.const false) (Stepped.walk (stepK (thetaU τ) 3) rootP (Stepped.mapOut (COUNTp ℓ) posZ)))
def StCore3Eq : Prop := ∀ ℓ τ : ℕ, ThreeSatPrinted.SATCp ℓ τ = Stepped.mapIn (fun x : List Bool => ((List.replicate (DecodeK.decK 3 x).1 (), (DecodeK.decK 3 x).2) : List Unit × Fml)) (core3 ℓ τ)
def StCore3 : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (core3 ℓ τ) ∧ ∃ c : ℕ, Decides3 (core3 ℓ τ) δ c
def SATsplit (k τ ℓ₃ τ₃ : ℕ) : StepMachine (List Bool) Bool := REDUCE k τ (core3 ℓ₃ τ₃)
def StSATsplit : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ τ ℓ₃ τ₃ : ℕ, PolyTimeSteps (SATsplit k τ ℓ₃ τ₃) ∧ ∃ c : ℕ, Decides (SATsplit k τ ℓ₃ τ₃) k δ c
def StTiedTM : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (τ ℓ₃ τ₃ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (SATsplit k τ ℓ₃ τ₃) ∧ Decides (SATsplit k τ ℓ₃ τ₃) k δ c ∧
  Simulates M (SATsplit k τ ℓ₃ τ₃) q ∧
  SatK.DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def StTiedThreeTM : Prop := ∀ δ : ℝ, 0 < δ → ∃ (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (ThreeSatPrinted.SATCp ℓ τ) ∧ Decides (ThreeSatPrinted.SATCp ℓ τ) 3 δ c ∧ Simulates M (ThreeSatPrinted.SATCp ℓ τ) q ∧ SatK.DecidesTM 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
abbrev ThreeSatStatement : Prop := PaperSentences.CorEth
end SplitSat


