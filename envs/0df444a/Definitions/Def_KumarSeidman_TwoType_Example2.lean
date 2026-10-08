-- Prove2me | Definitions.Def_KumarSeidman_TwoType_Example2
-- name    : KumarSeidman_TwoType_Example2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:37.689326+00:00
-- url     : https://prove2.me/theorems/d2a5ee84-c974-46b3-bc89-b3406d944773
-- title:
--   Example 2, Fig. 3, pp. 292–293 — the two-part-type, two-machine system
-- statement:
--   This module defines the system of Example 2 (Fig. 3) as a function of eight real parameters $\tau_1,\tau_2,\tau_3,\tau_4,\delta_1,\delta_2,\delta_3,\delta_4$.
--
--   There are two part types and two machines, and both part types have input rate $1$.
--
--   1. Part type 1 first visits buffer 1 at machine 1 and then buffer 2 at machine 2.
--   2. Part type 2 first visits buffer 3 at machine 2 and then buffer 4 at machine 1.
--
--   So $B_1=\{b_1,b_4\}$ and $B_2=\{b_2,b_3\}$. No part type revisits a machine, but material flows from machine 1 to machine 2 and back. The processing times of buffers 1–4 are $\tau_1,\dots,\tau_4$, and setting up to buffer $k$ takes $\delta_k$:
--   $$
--   \delta_{b_4,b_1}=\delta_1,\quad \delta_{b_3,b_2}=\delta_2,\quad \delta_{b_2,b_3}=\delta_3,\quad \delta_{b_1,b_4}=\delta_4 .
--   $$
--   The module also names buffers $b_1,\dots,b_4$ and machines $m_1,m_2$, writes a level vector as $(a_1,a_2,a_3,a_4)$, and writes the initial set-ups of the two machines as a pair.
--
--   **Formalization Note** Set-up times depend only on the target buffer, as in the paper ("the times for setting-up to these buffers are $\delta_1,\delta_2,\delta_3,\delta_4$"). Staying on the same buffer costs $0$; a clearing policy never uses that value. Machines 1, 2 are Lean `0, 1`; part types 1, 2 are Lean `0, 1`.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, pp. 292–293, Example 2, Fig. 3

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Clearing

namespace KumarSeidman.TwoType

/-- The system of Example 2 (Fig. 3, pp. 292–293). There are two part types and two machines
(Lean `0, 1` are the paper's machines 1, 2), both input rates are `1`, and every route has two
stages:

* part type 1 (Lean `0`) visits buffer 1 at machine 1 and then buffer 2 at machine 2;
* part type 2 (Lean `1`) visits buffer 3 at machine 2 and then buffer 4 at machine 1.

The processing times of buffers 1–4 are `τ₁, τ₂, τ₃, τ₄`. Setting up to buffer `k` takes `δ_k`
whatever buffer the machine leaves (`δ_{b,b'}` depends only on the target `b'`); staying on the
same buffer costs nothing (`δ_{b,b} = 0`, a value never used by a clearing policy). -/
noncomputable def example2 (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ) : System where
  P := 2
  M := 2
  n := fun _ => 2
  μ := fun p i => ![![0, 1], ![1, 0]] p i
  d := fun _ => 1
  τ := fun p i => ![![τ₁, τ₂], ![τ₃, τ₄]] p i
  δ := fun b b' => if b = b' then 0 else ![![δ₁, δ₂], ![δ₃, δ₄]] b'.1 b'.2

namespace Example2

variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}

/-- Buffer 1 of Example 2 (part type 1, first stage; at machine 1). -/
def b₁ : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer := ⟨(0 : Fin 2), (0 : Fin 2)⟩
/-- Buffer 2 of Example 2 (part type 1, second stage; at machine 2). -/
def b₂ : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer := ⟨(0 : Fin 2), (1 : Fin 2)⟩
/-- Buffer 3 of Example 2 (part type 2, first stage; at machine 2). -/
def b₃ : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer := ⟨(1 : Fin 2), (0 : Fin 2)⟩
/-- Buffer 4 of Example 2 (part type 2, second stage; at machine 1). -/
def b₄ : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer := ⟨(1 : Fin 2), (1 : Fin 2)⟩

/-- Machine 1 of Example 2 (it holds buffers 1 and 4). -/
def m₁ : Fin (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).M := (0 : Fin 2)
/-- Machine 2 of Example 2 (it holds buffers 2 and 3). -/
def m₂ : Fin (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).M := (1 : Fin 2)

/-- The vector of buffer levels `(a₁, a₂, a₃, a₄)` (level `a_k` in buffer `k`). -/
def levels (a₁ a₂ a₃ a₄ : ℝ) : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer → ℝ :=
  fun b => ![![a₁, a₂], ![a₃, a₄]] b.1 b.2

/-- The initial set-up assigning buffer `c₁` to machine 1 and buffer `c₂` to machine 2. -/
def setups (c₁ c₂ : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer) :
    Fin (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).M → (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer :=
  fun m => ![c₁, c₂] m

end Example2

end KumarSeidman.TwoType


