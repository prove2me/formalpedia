-- Prove2me | Definitions.Def_ConservativePJ_ManyPlayers_OneBitSelection
-- name    : ConservativePJ_ManyPlayers_OneBitSelection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:09.213538+00:00
-- url     : https://prove2.me/theorems/ef089888-6066-4059-9e21-660aceb55dda
-- title:
--   One-bit selection (§1.2, §3): one-bit protocols with public randomness, the receiver's success probability at a coordinate, and the marginals $p_i$
-- statement:
--   In the **one-bit selection problem** a sender and a receiver share a public random string, independent of everything else. The sender sees two independent and identically distributed random vectors $V,V'\in\{0,1\}^d$, whose coordinates may be correlated in any way, and sends one bit; the receiver sees a coordinate $i\in[d]$ and the bit, and chooses $V$ or $V'$. It **succeeds at $i$** if the chosen vector has a one at coordinate $i$. With $p_i=\Pr[V_i=1]$, the success probability at $i$ minus $p_i$ is the gain at $i$.
--
--   A **one-bit protocol with public randomness** consists of a public random string $\omega$ uniform on a finite set, a sender map $(\omega,V,V')\mapsto$ bit, and a receiver map $(\omega,i,\text{bit})\mapsto\{V,V'\}$. It depends only on $d$: neither map refers to the law of $(V,V')$.
--
--   **Formalization Note.** `OneBitProtocol d`: the string is uniform on `Fin R` ($R\ge1$), `send ω V V'` is the bit, and `choose ω i b = true` means the receiver chooses $V$. A law of $V$ on $\{0,1\}^d$ (`Fin d → Bool`) is a probability mass function `ν` (`IsPMF ν`); `successAt Q ν i` $=\sum_{\omega,v,v'}\frac1R\,\nu(v)\nu(v')\,[\text{chosen vector has a one at }i]$; `marginal ν i` $=p_i$. The paper's selector (Definition 3.1, App. A.1) is of this form, with $d+\lceil\log(d+1)/2\rceil+7$ uniform public bits.
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), pp. 3–4 (PDF 5–6), §1.2 One-bit selection; p. 8 (PDF 10), §3; p. 16 (PDF 18), App. A.1 (implementation with finitely many coins)

import Mathlib

set_option autoImplicit false

namespace ConservativePJ.ManyPlayers

open Finset

/-! Mantri, *Tight Bounds for Conservative Pointer Jumping*, STOC 2027 submission (manuscript sha256
5f73a9aa…), §1.2 (pp. 3–4) and §3 (p. 8): the one-bit selection problem. -/

/-- A one-bit protocol with public randomness for one-bit selection over `d` coordinates. The
public random string is uniform on a finite set `Fin R` (`R ≥ 1`) and independent of the vectors.
The sender sees the string and the two vectors `V, V' ∈ {0,1}^d` and sends one bit
`send ω V V'`; the receiver sees the string, a coordinate `i ∈ [d]` (as `Fin d`) and the bit, and
chooses `V` when `choose ω i b = true` and `V'` otherwise. Nothing in it refers to the law of the
vectors: it depends only on `d`. -/
structure OneBitProtocol (d : ℕ) where
  R : ℕ
  R_pos : 0 < R
  send : Fin R → (Fin d → Bool) → (Fin d → Bool) → Bool
  choose : Fin R → Fin d → Bool → Bool

namespace OneBitProtocol

variable {d : ℕ}

/-- The value at coordinate `i` of the vector that the receiver chooses. -/
def chosenBit (Q : OneBitProtocol d) (ω : Fin Q.R) (i : Fin d) (v v' : Fin d → Bool) : Bool :=
  if Q.choose ω i (Q.send ω v v') then v i else v' i

/-- The probability that the receiver succeeds at coordinate `i` (the chosen vector has a one at
`i`) when `V, V'` are independent with law `ν` on `{0,1}^d` (a probability mass function, given by
its weights) and the public string is uniform and independent of them. -/
noncomputable def successAt (Q : OneBitProtocol d) (ν : (Fin d → Bool) → ℝ) (i : Fin d) : ℝ :=
  ∑ ω : Fin Q.R, ∑ v : Fin d → Bool, ∑ v' : Fin d → Bool,
    (1 / (Q.R : ℝ)) * ν v * ν v' * (if Q.chosenBit ω i v v' then 1 else 0)

end OneBitProtocol

/-- `ν` is a probability mass function on `{0,1}^d` (an arbitrary joint law of the coordinates). -/
def IsPMF {d : ℕ} (ν : (Fin d → Bool) → ℝ) : Prop :=
  (∀ v, 0 ≤ ν v) ∧ ∑ v, ν v = 1

/-- The marginal `p_i = Pr[V_i = 1]` of the law `ν`. -/
noncomputable def marginal {d : ℕ} (ν : (Fin d → Bool) → ℝ) (i : Fin d) : ℝ :=
  ∑ v : Fin d → Bool, ν v * (if v i then 1 else 0)

end ConservativePJ.ManyPlayers


