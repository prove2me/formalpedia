-- Prove2me | Definitions.Def_StableCount_Potential
-- name    : StableCount_Potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:51.483134+00:00
-- url     : https://prove2.me/theorems/6343e687-3525-47c0-a942-22a80d4a69cb
-- title:
--   Branching potentials, admissible sequences (Definition 4.1), $F_h$ and the losses $p^*$, $q^*$
-- statement:
--   A nonnegative function $F$ on a family containing $\emptyset$, with $F(\emptyset)=0$, is a **branching potential** if every nonempty $Q$ has $Q_1,Q_2$ of smaller size with $J(Q)=J(Q_1)+J(Q_2)$ and $e^{F(Q_1)}+e^{F(Q_2)}\le e^{F(Q)}$.
--
--   Let $h_1\ge h_2\ge\dots>0$, and set $W(d)=\sum_{r=1}^d h_r$, $H_d=\sum_{r=1}^d (r+1)h_r$, with $W(0)=H_0=0$, and $\lambda(t)=-\ln(1-e^{-t})$ for $t>0$. With $A_1=4h_1$ and $A_c=H_c+h_1+2h_2$ for $c\ge 2$, the sequence is **admissible** if
--
--   1. (H1) $2h_1\ge\ln 2$;
--   2. (H2) $\lambda(2h_d)\le H_d+h_2$ for every $d\ge 2$;
--   3. (H3) $\lambda(2h_a)+\lambda(h_{a-1}+2h_a+h_c)\le H_a+A_c$ for every $a\ge 3$ and $c\ge 1$;
--   4. (H4) $h_1\ge 2h_2$, $2h_3\ge h_2$ and $4h_1-\lambda(h_1)\ge h_2$;
--   5. (H5) $h_3\le 1/10$ and $h_2\le 8h_3/5$.
--
--   For $Q\in\mathcal Q$,
--   $$
--   F_h(Q)=\frac12\sum_{v=1}^n\big(W(d^m_v)+W(d^w_v)\big).
--   $$
--   For one sex, $F(Q)=\sum_v W(d_v)$, $p(\rho)=F(Q)-F(Q\setminus\downarrow\rho)$, $q(\rho)=F(Q)-F(Q\setminus\uparrow\rho)$, and $p^*,q^*$ are the averages of the two sexes' losses. The active labels are $V=\{v:d^m_v>0\}$, and $b_v$ is the first rotation of the active label $v$.
--
--   These are the potential and the sufficient conditions on which the induction of the paper runs.
--
--   **Formalization Note** `h : ℕ → ℝ` with `h 0` never read. In Lean `lam 0 = 0`; this is never hit, as all arguments are positive for an admissible sequence. The potential of a smaller member is computed from $Q$ by `Fon`, from the retained counts: Lemma 3.7 gives the degrees and relabelling women does not change the sum. `IsBranchingPotential` is generic over an indexed family.
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), §1.2, pp.4–5; §4.1, p.13; §4.2, pp.14–15

import Mathlib
import Definitions.Def_StableCount_Member

namespace StableCount

variable {n : ℕ}

/-- Branching potential (arXiv:2611.06494, held PDF sha256 9445f6a8…, §1.2, pp.4–5): on a family
containing an empty member, a nonnegative `F` with `F(∅) = 0` such that every nonempty `a` has
`a₁, a₂` of smaller size with `J(a) = J(a₁) + J(a₂)` and `e^{F(a₁)} + e^{F(a₂)} ≤ e^{F(a)}`, display (1).

**Formalization Note** Generic over an indexed family: a member of `𝒬` is a poset with its data, not
a bare poset (`Member`), so size and `J` are passed as functions. -/
def IsBranchingPotential {α : Type*} (size J : α → ℕ) (F : α → ℝ) : Prop :=
  (∃ a, size a = 0) ∧ (∀ a, 0 ≤ F a) ∧ (∀ a, size a = 0 → F a = 0) ∧
    ∀ a, size a ≠ 0 → ∃ a₁ a₂, size a₁ < size a ∧ size a₂ < size a ∧ J a = J a₁ + J a₂ ∧
      Real.exp (F a₁) + Real.exp (F a₂) ≤ Real.exp (F a)

/-- `W(d) = ∑_{r=1}^d h_r`, with `W(0) = 0` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.1, p.13). -/
noncomputable def W (h : ℕ → ℝ) (d : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 d, h r

/-- `H_d = ∑_{r=1}^d (r + 1) h_r`, with `H₀ = 0` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.1,
p.13). -/
noncomputable def Hsum (h : ℕ → ℝ) (d : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 d, ((r : ℝ) + 1) * h r

/-- `λ(t) = −ln(1 − e^{−t})`, for `t > 0` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.1, p.13).

**Formalization Note** At `t = 0` Lean gives `Real.log 0 = 0`, so `lam 0 = 0` rather than `+∞`. This
is never hit: `λ` is applied to losses and sums of weights, which are positive for an admissible
sequence ("Every loss is positive", p.15). -/
noncomputable def lam (t : ℝ) : ℝ := -Real.log (1 - Real.exp (-t))

/-- `A₁ = 4h₁` and `A_c = H_c + h₁ + 2h₂` for `c ≥ 2` (arXiv:2611.06494, held PDF sha256 9445f6a8…,
Definition 4.1, p.13). -/
noncomputable def Aval (h : ℕ → ℝ) (c : ℕ) : ℝ :=
  if c = 1 then 4 * h 1 else Hsum h c + h 1 + 2 * h 2

/-- (H1) `2h₁ ≥ ln 2` (arXiv:2611.06494, held PDF sha256 9445f6a8…, Definition 4.1, p.13). -/
def CondH1 (h : ℕ → ℝ) : Prop := Real.log 2 ≤ 2 * h 1

/-- (H2) `λ(2h_d) ≤ H_d + h₂` for every `d ≥ 2` (arXiv:2611.06494, held PDF sha256 9445f6a8…,
Definition 4.1, p.13). -/
def CondH2 (h : ℕ → ℝ) : Prop := ∀ d, 2 ≤ d → lam (2 * h d) ≤ Hsum h d + h 2

/-- (H3) `λ(2h_a) + λ(h_{a−1} + 2h_a + h_c) ≤ H_a + A_c` for every `a ≥ 3` and `c ≥ 1`
(arXiv:2611.06494, held PDF sha256 9445f6a8…, Definition 4.1, p.13). -/
def CondH3 (h : ℕ → ℝ) : Prop :=
  ∀ a c, 3 ≤ a → 1 ≤ c →
    lam (2 * h a) + lam (h (a - 1) + 2 * h a + h c) ≤ Hsum h a + Aval h c

/-- (H4) `h₁ ≥ 2h₂`, `2h₃ ≥ h₂` and `4h₁ − λ(h₁) ≥ h₂` (arXiv:2611.06494, held PDF sha256 9445f6a8…,
Definition 4.1, p.13). -/
def CondH4 (h : ℕ → ℝ) : Prop :=
  2 * h 2 ≤ h 1 ∧ h 2 ≤ 2 * h 3 ∧ h 2 ≤ 4 * h 1 - lam (h 1)

/-- (H5) `h₃ ≤ 1/10` and `h₂ ≤ 8h₃/5` (arXiv:2611.06494, held PDF sha256 9445f6a8…, Definition 4.1,
p.13). -/
def CondH5 (h : ℕ → ℝ) : Prop := h 3 ≤ 1 / 10 ∧ h 2 ≤ 8 * h 3 / 5

/-- Definition 4.1: a sequence `h₁ ≥ h₂ ≥ ⋯ > 0` satisfying (H1)–(H5) (arXiv:2611.06494, held PDF
sha256 9445f6a8…, Definition 4.1, p.13).

**Formalization Note** `h : ℕ → ℝ` with `h 0` unused: every clause reads indices `≥ 1` only. -/
def IsAdmissible (h : ℕ → ℝ) : Prop :=
  (∀ d, 1 ≤ d → 0 < h d) ∧ (∀ d, 1 ≤ d → h (d + 1) ≤ h d) ∧
    CondH1 h ∧ CondH2 h ∧ CondH3 h ∧ CondH4 h ∧ CondH5 h

namespace Member

variable (Q : Member n)

/-- `F_h(Q) = ½ ∑_{v=1}^n (W(dᵐ_v) + W(dʷ_v))` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.1,
p.13). -/
noncomputable def Fh (h : ℕ → ℝ) : ℝ :=
  (1 / 2) * ∑ v, (W h (Q.dL .man v) + W h (Q.dL .woman v))

/-- The one-sex potential of the retained set `P`: `∑_{v=1}^n W(d_v)` with degrees the retained
occurrences (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.2, p.15).

**Formalization Note** A loss compares `Q` with the smaller member `Q \ ↓ρ` or `Q \ ↑ρ`. This
function computes the smaller member's one-sex potential from `Q`: Lemma 3.7 gives its degrees as the
retained counts, and relabelling women does not change the sum (p.15). -/
noncomputable def Fon (h : ℕ → ℝ) (s : Sex) (P : Finset (Fin Q.R)) : ℝ :=
  ∑ v, W h (Q.degOn P s (Q.person s v))

/-- `p(ρ) = F(Q) − F(Q \ ↓ρ)` for sex `s` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.2, p.15). -/
noncomputable def pLoss (h : ℕ → ℝ) (s : Sex) (i : Fin Q.R) : ℝ :=
  Q.Fon h s Finset.univ - Q.Fon h s (Finset.univ \ Q.down i)

/-- `q(ρ) = F(Q) − F(Q \ ↑ρ)` for sex `s` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.2, p.15). -/
noncomputable def qLoss (h : ℕ → ℝ) (s : Sex) (i : Fin Q.R) : ℝ :=
  Q.Fon h s Finset.univ - Q.Fon h s (Finset.univ \ Q.up i)

/-- `p*(ρ) = (pᵐ(ρ) + pʷ(ρ))/2` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.2, p.15). -/
noncomputable def pStar (h : ℕ → ℝ) (i : Fin Q.R) : ℝ :=
  (Q.pLoss h .man i + Q.pLoss h .woman i) / 2

/-- `q*(ρ) = (qᵐ(ρ) + qʷ(ρ))/2` (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.2, p.15). -/
noncomputable def qStar (h : ℕ → ℝ) (i : Fin Q.R) : ℝ :=
  (Q.qLoss h .man i + Q.qLoss h .woman i) / 2

/-- `V = {v : dᵐ_v > 0}`, the active labels (arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.2, p.15).
The equality with `{v : dʷ_v > 0}` is Lemma 3.4. -/
def V : Finset (Fin n) := Finset.univ.filter fun v => 0 < Q.dL .man v

/-- `b_v`, the first rotation of the active label `v`, read on the man with label `v`
(arXiv:2611.06494, held PDF sha256 9445f6a8…, §4.2, p.15). By Lemma 3.4 it is also the first rotation
of the woman with label `v`. -/
def first (v : Fin n) (hv : v ∈ Q.V) : Fin Q.R :=
  (Q.chainOf .man v).min' (Finset.card_pos.mp (Finset.mem_filter.mp hv).2)

/-- `f(b_v)` for a label `v`.

**Formalization Note** The value `0` on an inactive label is never hit: every use is for a label of
`V`. The sums `∑_{v ∈ V} atFirst f v` count labels sharing a first rotation separately, as on p.15. -/
def atFirst (f : Fin Q.R → ℝ) (v : Fin n) : ℝ :=
  if hv : v ∈ Q.V then f (Q.first v hv) else 0

end Member

end StableCount


