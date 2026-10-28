-- Prove2me | Definitions.Def_CH_Cohen_Reduct
-- name    : CH_Cohen_Reduct
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T02:13:30.862532+00:00
-- url     : https://prove2.me/theorems/e7c45dec-b911-41f4-abf1-66a581e3f60b
-- title:
--   The membership reduct of the expanded set-theory language
-- statement:
--   For an ordinary structure $M$ in Flypitch’s expanded set-theory language, retain the same carrier, equality and membership relation, and forget the five function symbols. This defines its reduct to the mission’s exact membership-only language. No axiom-satisfaction or CH-preservation assertion is built into this definition.
--
--   The original forcing formalization is by Jesse Han and Floris van Doorn. The Lean 4 port is by Ian Klatzco, with Claude, under Apache-2.0. This compatibility statement connects that development to the mission’s existing definitions.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, A Formal Proof of the Independence of the Continuum Hypothesis, CPP 2020, §2.2 and Figure 1, and §7 (the membership-language transfer is listed as future work), https://florisvandoorn.com/papers/flypitch-cpp-2020.pdf; Ian Klatzco Lean 4 port, commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815, Flypitch4/Zfc.lean; mission definitions CH_SetTheoryLanguage and CH_ZFC. Explicit semantic compatibility obligations for those two axiom and sentence presentations.

import Definitions.Def_CH_Cohen_Library10
import Definitions.Def_CH_ZFC

/-!
The membership reduct of Flypitch's expanded set-theory language.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

Sources: Jesse Han and Floris van Doorn, Flypitch, CPP 2020, §§2.2 and 7;
Ian Klatzco's Lean 4 port, commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815,
Flypitch4/Zfc.lean and Flypitch4/Fol.lean. Original sources are Apache-2.0.
-/

namespace ContinuumHypothesis.Cohen

/-- Forget the five function symbols, retaining exactly the membership relation. -/
def membershipReduct (M : Fol.Structure _root_.L_ZFC) :
    setLang.Structure M.carrier where
  funMap := fun f => Empty.elim f
  RelMap := fun r v => match r with
    | SetRel.mem => M.rel_map _root_.ZFC_rel.ε
        (DVec.cons (v 0) (DVec.cons (v 1) DVec.nil))

end ContinuumHypothesis.Cohen


