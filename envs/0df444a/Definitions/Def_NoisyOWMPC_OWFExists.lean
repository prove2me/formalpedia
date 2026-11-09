-- Prove2me | Definitions.Def_NoisyOWMPC_OWFExists
-- name    : NoisyOWMPC_OWFExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:54:59.07285+00:00
-- url     : https://prove2.me/theorems/717500bc-527f-48d6-a2ba-d6bcb96cff81
-- title:
--   One-way functions exist
-- statement:
--   **One-way functions exist** if there is an efficiently computable function family without keys satisfying the one-wayness clause of Definition 3.3 against nonuniform polynomial-size inverters.
--
--   This is the hypothesis "one-way functions" of Theorem 3.4 and of the main theorem.
--
--   **Formalization Note** It is the one-wayness clause of Definition 3.3 with key length zero and without injectivity.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem 3.4, p.16; Theorem 5.24, p.30

import Mathlib
import Definitions.Def_NoisyOWMPC_KeyedFamily

namespace NoisyOWMPC

/-- **One-way functions exist** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), Theorem 3.4, p.16, and Theorem 5.24, p.30: "Under … iO, and one-way functions"): there
is an efficiently computable function family, with no key (key length `0`), satisfying the
one-wayness clause of Definition 3.3 against nonuniform polynomial-size inverters.

**Formalization Note** This is the standard assumption "one-way functions exist": the one-wayness
clause of Definition 3.3 without keys and without injectivity. -/
def OWFExists : Prop :=
  ∃ F : KeyedFamily, F.Efficient ∧ F.OneWay ∧ ∀ lam, F.kl lam = 0

end NoisyOWMPC


