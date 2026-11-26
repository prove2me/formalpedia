-- Prove2me | Definitions.Def_SATLocalQueryDetector
-- name    : SATLocalQueryDetector
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T21:46:11.789015+00:00
-- url     : https://prove2.me/theorems/c186d759-db69-40e7-8db6-e418c1341602
-- title:
--   Adaptive binary queries to a singleton oracle
-- statement:
--   An adaptive detector is a binary query tree. An internal node queries an input point and selects a subtree using the oracle's Boolean response. A leaf returns an output. The singleton oracle returns true at exactly its designated target.
-- source:
--   Deterministic oracle decision trees.

import Mathlib

set_option autoImplicit false

namespace SATLocalQuery

/-- An adaptive detector may use every previous reply when choosing its
next oracle query.  The output is independent of replies absent from its trace. -/
inductive Detector (I O : Type*) where
  | result : O → Detector I O
  | ask : I → (Bool → Detector I O) → Detector I O

namespace Detector

variable {I O : Type*}

def run (oracle : I → Bool) : Detector I O → O
  | .result output => output
  | .ask i next => run oracle (next (oracle i))

def calls (oracle : I → Bool) : Detector I O → List I
  | .result _ => []
  | .ask i next => i :: calls oracle (next (oracle i))

def onlyAt [DecidableEq I] (target : I) : I → Bool :=
  fun i => decide (i = target)

end Detector
end SATLocalQuery


