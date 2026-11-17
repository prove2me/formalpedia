-- Prove2me | Definitions.Def_AvoidPlast_Supplement_InDTIME
-- name    : AvoidPlast_Supplement_InDTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:46:49.739434+00:00
-- url     : https://prove2.me/theorems/d34136f7-3f47-40b8-a9af-9a4afaf9fea6
-- title:
--   The class $\mathrm{DTIME}[t(n)]$
-- statement:
--   A language $L$ is in $\mathrm{DTIME}[t(n)]$ if a deterministic machine of the RAM model halts on every $n$-bit input within $C\cdot(t(n)+1)$ steps for a constant $C$ and accepts exactly the strings of $L$.
--
--   With random access to the input, sub-linear time bounds such as $t(n)=\lceil n^{\varepsilon}\rceil$ are meaningful; Theorem 5.1 uses them.
--
--   **Formalization Note** The $+1$ covers $t(n)=0$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 5.1 and 5.4, pp.21–23 (PDF pp.23–25)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `L ∈ DTIME[t(n)]` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 5.1 and 5.4, pp.21–23): a deterministic machine (RAM
model, reading R5) halting within `C · (t(n) + 1)` steps decides `L`. The `+ 1` covers `t(n) = 0`. -/
def InDTIME (t : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∃ (M : Machine 1) (C : ℕ), (∀ x : List Bool, HaltsWithin M ![x] (C * (t x.length + 1))) ∧
    ∀ x : List Bool, Accepts M ![x] ↔ x ∈ L

end AvoidPlast.Supplement


