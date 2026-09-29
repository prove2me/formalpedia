-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_JetProgramShape
-- name    : CK_GeneralCK_Certificates_JetProgramShape
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:28:07.941701+00:00
-- url     : https://prove2.me/theorems/2766b073-882a-454c-88df-bfdd9b4993fd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.JetProgramShape` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.JetProgramShape` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.JetProgramShape` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.JetProgramShape (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/JetProgramShape.lean)

import Definitions.Def_CK_GeneralCK_Certificates_JetProgramValues

namespace GeneralCK.Certificates.JetProgram

/-- Numerical certificate data have no place in the expression being proved. -/
inductive ShapeOp where
  | add (left right : ℕ)
  | neg (arg : ℕ)
  | mul (left right : ℕ)
  | inv (arg : ℕ)
  | log (arg : ℕ)
  | contact (arg : ℕ)
  deriving DecidableEq, Repr

def Op.shape {p : ℕ} : Op p → ShapeOp
  | .add i j => .add i j
  | .neg i => .neg i
  | .mul i j => .mul i j
  | .inv i => .inv i
  | .log i _ _ => .log i
  | .contact i _ _ _ _ _ => .contact i

noncomputable def ShapeOp.eval (op : ShapeOp) (jets : List Jet2) : Jet2 := match op with
  | .add i j => (jets.getD i zeroJet).add (jets.getD j zeroJet)
  | .neg i => (jets.getD i zeroJet).neg
  | .mul i j => (jets.getD i zeroJet).mul (jets.getD j zeroJet)
  | .inv i => (jets.getD i zeroJet).inv
  | .log i => (jets.getD i zeroJet).log
  | .contact i => reflectionContactJet.comp (jets.getD i zeroJet)

theorem Op.eval_eq_shape {p : ℕ} (op : Op p) (jets : List Jet2) :
    op.eval jets=op.shape.eval jets := by cases op <;> rfl

def programShape {p : ℕ} (program : List (Instruction p)) : List ShapeOp :=
  program.map (fun ins => ins.op.shape)

noncomputable def evalShapes : List ShapeOp → List Jet2 → List Jet2
  | [], jets => jets
  | op :: rest, jets => evalShapes rest (op.eval jets :: jets)

theorem finalJets_eq_evalShapes {p : ℕ} (program : List (Instruction p)) (jets : List Jet2) :
    finalJets program jets=evalShapes (programShape program) jets := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih =>
    simpa only [finalJets,programShape,List.map_cons,evalShapes,Op.eval_eq_shape] using
      ih (ins.op.eval jets :: jets)

/-- Center and whole-box certificates with the same operations describe identical jets,
even if they use different precision and entirely different numerical witnesses. -/
theorem finalJets_eq_of_programShape {p q : ℕ} (first : List (Instruction p))
    (second : List (Instruction q)) (h : programShape first=programShape second) (jets : List Jet2) :
    finalJets first jets=finalJets second jets := by
  rw [finalJets_eq_evalShapes,finalJets_eq_evalShapes,h]

noncomputable def ShapeOp.evalReal (op : ShapeOp) (values : List ℝ) : ℝ := match op with
  | .add i j => values.getD i 0+values.getD j 0
  | .neg i => -values.getD i 0
  | .mul i j => values.getD i 0*values.getD j 0
  | .inv i => (values.getD i 0)⁻¹
  | .log i => Real.log (values.getD i 0)
  | .contact i => GeneralCK.Reflection.biasContact (values.getD i 0)

theorem ShapeOp.eval_value (op : ShapeOp) (jets : List Jet2) (t : ℝ) :
    (op.eval jets).value t=op.evalReal (jets.map (fun j => j.value t)) := by
  cases op <;> simp only [ShapeOp.eval,ShapeOp.evalReal,Jet2.add,Jet2.neg,Jet2.mul,Jet2.inv,
    Jet2.log,Jet2.comp,reflectionContactJet,value_getD]

noncomputable def evalRealShapes : List ShapeOp → List ℝ → List ℝ
  | [], values => values
  | op :: rest, values => evalRealShapes rest (op.evalReal values :: values)

theorem evalShapes_values (ops : List ShapeOp) (jets : List Jet2) (t : ℝ) :
    (evalShapes ops jets).map (fun j => j.value t)=
      evalRealShapes ops (jets.map (fun j => j.value t)) := by
  induction ops generalizing jets with
  | nil => rfl
  | cons op rest ih =>
    simpa only [evalShapes,evalRealShapes,List.map_cons,ShapeOp.eval_value] using
      ih (op.eval jets :: jets)

theorem evalShape_value (ops : List ShapeOp) (jets : List Jet2) (i : ℕ) (t : ℝ) :
    ((evalShapes ops jets).getD i zeroJet).value t=
      (evalRealShapes ops (jets.map (fun j => j.value t))).getD i 0 := by
  rw [value_getD,evalShapes_values]

end GeneralCK.Certificates.JetProgram


