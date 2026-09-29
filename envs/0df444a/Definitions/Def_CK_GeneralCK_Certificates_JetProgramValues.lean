-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_JetProgramValues
-- name    : CK_GeneralCK_Certificates_JetProgramValues
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:24:33.833589+00:00
-- url     : https://prove2.me/theorems/e3341b6f-df4b-4d48-b8df-63561d405cd9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.JetProgramValues` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.JetProgramValues` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.JetProgramValues` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.JetProgramValues (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/JetProgramValues.lean)

import Definitions.Def_CK_GeneralCK_Certificates_JetProgram

namespace GeneralCK.Certificates.JetProgram

/-- Scalar semantics allow expression matching without expanding unused derivative fields. -/
noncomputable def Op.evalReal {p : ℕ} (op : Op p) (values : List ℝ) : ℝ := match op with
  | .add i j => values.getD i 0+values.getD j 0
  | .neg i => -values.getD i 0
  | .mul i j => values.getD i 0*values.getD j 0
  | .inv i => (values.getD i 0)⁻¹
  | .log i _ _ => Real.log (values.getD i 0)
  | .contact i _ _ _ _ _ => GeneralCK.Reflection.biasContact (values.getD i 0)

theorem value_getD (jets : List Jet2) (i : ℕ) (t : ℝ) :
    (jets.getD i zeroJet).value t=(jets.map (fun j => j.value t)).getD i 0 := by
  induction jets generalizing i with
  | nil => simp [zeroJet,Jet2.const]
  | cons j jets ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem Op.eval_value {p : ℕ} (op : Op p) (jets : List Jet2) (t : ℝ) :
    (op.eval jets).value t=op.evalReal (jets.map (fun j => j.value t)) := by
  cases op <;> simp only [Op.eval,Op.evalReal,Jet2.add,Jet2.neg,Jet2.mul,Jet2.inv,Jet2.log,
    Jet2.comp,reflectionContactJet,value_getD]

noncomputable def evalRealProgram {p : ℕ} : List (Instruction p) → List ℝ → List ℝ
  | [], values => values
  | ins :: rest, values => evalRealProgram rest (ins.op.evalReal values :: values)

theorem finalJets_values {p : ℕ} (program : List (Instruction p)) (jets : List Jet2) (t : ℝ) :
    (finalJets program jets).map (fun j => j.value t)=
      evalRealProgram program (jets.map (fun j => j.value t)) := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih =>
    simpa only [finalJets,evalRealProgram,List.map_cons,Op.eval_value] using
      ih (ins.op.eval jets :: jets)

theorem finalJet_value {p : ℕ} (program : List (Instruction p)) (jets : List Jet2) (i : ℕ) (t : ℝ) :
    ((finalJets program jets).getD i zeroJet).value t=
      (evalRealProgram program (jets.map (fun j => j.value t))).getD i 0 := by
  rw [value_getD,finalJets_values]

end GeneralCK.Certificates.JetProgram


