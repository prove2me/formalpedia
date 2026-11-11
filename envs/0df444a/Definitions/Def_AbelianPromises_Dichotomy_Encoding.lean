-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Encoding
-- name    : AbelianPromises_Dichotomy_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:08:59.950373+00:00
-- url     : https://prove2.me/theorems/d61d64de-ce3b-4ffa-96cc-8071304ec5f1
-- title:
--   Binary encodings of instances and explicit colourings
-- statement:
--   An instance I with n variables is encoded by n in unary followed by binary indices for each ordered variable triple, using the published self-delimiting field encoding. All n variables are recorded even when they do not occur in a constraint. A colouring is an explicit list of n colour indices. Let enc(I) be this encoding. The two promise sets are
--   $$
--   \mathrm{YES}_R=\{\operatorname{enc}(I):I\text{ has an }R\text{-solution}\},\qquad
--   \mathrm{NO}_Q=\{\operatorname{enc}(I):I\text{ has no }Q\text{-solution}\}.
--   $$
--   Malformed encodings are in neither promise set. ColourSolution requires an explicitly encoded colouring satisfying every not-all-equal constraint. These encodings make input length and output writing cost precise, while retaining empty instances, isolated variables and repeated coordinates.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, Abelian embeddings make useful promises: approximation of detrivialised equations, STOC 2027 submission #967 (October 2026), printed p. 5 (PDF p. 6), §2 and Definition 2.1 (encoding convention)

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Relations
import Definitions.Def_MultiAccessLogspace_Halting_Encoding

set_option autoImplicit false

namespace AbelianPromises.Dichotomy

open MultiAccessLogspace.Halting

/-- List every variable in unary, then every ordered constraint by three binary indices.
Constraint repetition has no effect on satisfaction. Empty and isolated instances are retained. -/
def encodeInstance (I : Instance) : List Bool :=
  encodeFields (List.replicate I.n true ::
    (List.ofFn fun j : Fin I.m =>
      [binary (I.scope j 0).val, binary (I.scope j 1).val,
       binary (I.scope j 2).val]).flatten)

/-- Explicit colour list. Colours are zero based: source colour i+1 is Lean colour i. -/
def encodeColouring {n c : ℕ} (a : Fin n → Fin c) : List Bool :=
  encodeFields ((List.ofFn a).map fun x => binary x.val)

def ColourSolution (I : Instance) (c : ℕ) (w : List Bool) : Prop :=
  ∃ a : Fin I.n → Fin c, w = encodeColouring a ∧
    ∀ j : Fin I.m, ¬ (a (I.scope j 0) = a (I.scope j 1) ∧
      a (I.scope j 1) = a (I.scope j 2))

/-- Malformed strings belong to neither promise set. -/
def Yes {A : Type} (R : Relation A) (s : List Bool) : Prop :=
  ∃ I : Instance, s = encodeInstance I ∧ Satisfiable I R

def No {B : Type} (Q : Relation B) (s : List Bool) : Prop :=
  ∃ I : Instance, s = encodeInstance I ∧ ¬ Satisfiable I Q

end AbelianPromises.Dichotomy


