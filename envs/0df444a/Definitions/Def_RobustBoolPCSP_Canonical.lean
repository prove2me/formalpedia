-- Prove2me | Definitions.Def_RobustBoolPCSP_Canonical
-- name    : RobustBoolPCSP_Canonical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:46.17821+00:00
-- url     : https://prove2.me/theorems/ef5cdc70-b96a-4876-aa45-dead9409667d
-- title:
--   $\mathrm{NAND}_r$, $\mathrm{NAE}_r$ and the canonical pairs $\mathsf A_k$, $\mathsf B_r$, $\mathsf C_t$
-- statement:
--   For $r\ge0$ let $\mathrm{NAND}_r=\{0,1\}^r\setminus\{1^r\}$ and $\mathrm{NAE}_r=\{0,1\}^r\setminus\{0^r,1^r\}$, and let $\mathrm{Ham}_r(S)$ be the set of tuples whose Hamming weight lies in $S$. For odd $k=2b+1\ge3$ and integers $r\ge2$, $t\ge3$, the canonical relation pairs are
--
--   $$\mathsf A_k=(\mathrm{Ham}_k(\{b+1\}),\mathrm{NAND}_k),\quad \mathsf B_r=(\mathrm{Ham}_r(\{0,1\}),\mathrm{NAND}_r),\quad \mathsf C_t=(\mathrm{Ham}_t(\{1\}),\mathrm{Ham}_t(\{0,\dots,t\}\setminus\{t-1\})),$$
--
--   and $\{\mathsf A_k,\mathsf B_r\}$, $\{\mathsf A_k,\mathsf C_t\}$ are the templates with both indicated pairs.
--
--   Every mixed symmetric template simulates one of these two canonical templates.
--
--   **Formalization Note** $b+1$ is written $(k+1)/2$. The definitions are stated for all parameters; the range restrictions are hypotheses of the theorems. $\mathrm{Ham}$ is the published `SymBoolPCSP.CFixing.Ham`.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §3.2, p.15 (NAND, NAE); §4.3, p.21 (A_k, B_r, C_t)

import Mathlib
import Definitions.Def_RobustBoolPCSP_Template
import Definitions.Def_SymBoolPCSP_CFixing_Basic

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing

/-- `NAND_r = {0,1}^r \ {1^r}` (§3.2, p.15). -/
def NAND (r : ℕ) : Set (Fin r → Bool) := {x | x ≠ fun _ => true}

/-- `NAE_r = {0,1}^r \ {0^r, 1^r}` (§3.2, p.15). -/
def NAE (r : ℕ) : Set (Fin r → Bool) := {x | x ≠ (fun _ => true) ∧ x ≠ (fun _ => false)}

/-- The strong relation of `𝖠_k = (Ham_k({b + 1}), NAND_k)` for odd `k = 2b + 1` (§4.3, p.21);
`b + 1 = (k + 1)/2`. -/
def AkP (k : ℕ) : Set (Fin k → Bool) := Ham k {(k + 1) / 2}

/-- The strong relation of `𝖡_r = (Ham_r({0, 1}), NAND_r)` (§4.3, p.21). -/
def BrP (r : ℕ) : Set (Fin r → Bool) := Ham r {0, 1}

/-- The strong relation of `𝖢_t = (Ham_t({1}), Ham_t({0, …, t} \ {t − 1}))` (§4.3, p.21). -/
def CtP (t : ℕ) : Set (Fin t → Bool) := Ham t {1}

/-- The weak relation of `𝖢_t`: `Ham_t({0, …, t} \ {t − 1})`, the tuples whose weight is not
`t − 1` (all weights are at most `t`). -/
def CtQ (t : ℕ) : Set (Fin t → Bool) := Ham t {w | w ≠ t - 1}

/-- The canonical template `{𝖠_k, 𝖡_r}` (§4.3, p.21), "the template with both indicated pairs". -/
def templateAB (k r : ℕ) : Template (Unit ⊕ Unit) Bool Bool :=
  Template.pair (AkP k) (NAND k) (BrP r) (NAND r)

/-- The canonical template `{𝖠_k, 𝖢_t}` (§4.3, p.21). -/
def templateAC (k t : ℕ) : Template (Unit ⊕ Unit) Bool Bool :=
  Template.pair (AkP k) (NAND k) (CtP t) (CtQ t)

end RobustBoolPCSP


