-- Prove2me | Definitions.Def_RandPurIso_Completion_PRSt
-- name    : RandPurIso_Completion_PRSt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:17.891811+00:00
-- url     : https://prove2.me/theorems/393256f3-3c1c-4d90-b177-2b6d97746d2f
-- title:
--   Path register $\mathcal R_t$ and recording register $\mathbf{St}=\bigoplus_{t\le T}\mathcal R_t$
-- statement:
--   With $\mathcal H=\mathcal H([N])$, the **ordered path register** is $\mathcal R_t=\mathcal H^{\otimes t}\otimes\overline{\mathcal H}^{\otimes t}$ with basis $|\vec x,\vec y\rangle=|x_1\dots x_t\rangle\otimes\overline{|y_1\dots y_t\rangle}$, and $\mathcal R_0=\mathrm{Span}\{|\varnothing\rangle\}$. The **recording register** is $\mathbf{St}=\bigoplus_{t=0}^T\mathcal R_t$, starting in $|\varnothing\rangle$. The module also provides the shape $\sum_z|z\rangle\langle x|\otimes F_t$ of maps $\mathcal H\otimes\mathcal R_t\to\mathcal H\otimes\mathcal R_{t+1}$ ($t<T$, zero on $\mathcal R_T$) shared by $PR$ and $\widetilde{PR}$, and the embedding of an operator on $\mathcal R_t$ into $\mathbf{St}$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.4, p. 23; Definition 3.13, p. 24

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **Ordered path register** `R_t = H^{⊗t} ⊗ conj(H)^{⊗t}`, `H = H([N])` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.4, p. 23):
basis `|x⃗, y⃗⟩ = |x₁…x_t⟩ ⊗ conj|y₁…y_t⟩`, repeated entries allowed. -/
abbrev Rt (N t : ℕ) := (Fin t → Fin N) × (Fin t → Fin N)

/-- **Recording register** `St = ⊕_{t=0}^{T} R_t` (Definition 3.13, p. 24). A basis label is a
length `t ≤ T` with a pair of length-`t` words. -/
abbrev PRSt (N T : ℕ) := Σ t : Fin (T + 1), Rt N t.val

/-- The empty recording `|∅⟩ ∈ R_0` (`R_0 = Span{|∅⟩}`). -/
def emptyRec (N T : ℕ) : PRSt N T := ⟨0, (Fin.elim0, Fin.elim0)⟩

/-- The initial state `|∅⟩` of the recording register ("The recording register starts in |∅⟩",
Definition 3.13). -/
def emptyRecInit (N T : ℕ) : PRSt N T → ℂ := fun r => if r = emptyRec N T then 1 else 0

/-- The operator on `H([N]) ⊗ St` that maps `|x⟩ ⊗ R_t` to `R_{t+1}` by the blocks
`Σ_{z} |z⟩⟨x| ⊗ F t z x` for `t < T`, and is zero on `H ⊗ R_T` (the shape of Definition 3.13 and of
`~PR`, p. 30). -/
def recordOp {N T : ℕ} (F : (t : ℕ) → Fin N → Fin N → Matrix (Rt N (t + 1)) (Rt N t) ℂ) :
    Matrix (Fin N × PRSt N T) (Fin N × PRSt N T) ℂ :=
  fun p q =>
    if h : q.2.1.val < T ∧ p.2.1.val = q.2.1.val + 1 then
      F q.2.1.val p.1 q.1 (cast (congrArg (Rt N) h.2) p.2.2) q.2.2
    else 0

/-- An operator `B` on `R_t` viewed as an operator on `St = ⊕ R_s` (zero on the other summands). -/
def blockAt {N T : ℕ} (t : ℕ) (B : Matrix (Rt N t) (Rt N t) ℂ) : Matrix (PRSt N T) (PRSt N T) ℂ :=
  fun r' r => if h : r'.1.val = t ∧ r.1.val = t then
      B (cast (congrArg (Rt N) h.1) r'.2) (cast (congrArg (Rt N) h.2) r.2) else 0

end RandPurIso.Completion


