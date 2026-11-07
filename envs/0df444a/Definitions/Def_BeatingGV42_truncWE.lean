-- Prove2me | Definitions.Def_BeatingGV42_truncWE
-- name    : BeatingGV42_truncWE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:26.96321+00:00
-- url     : https://prove2.me/theorems/f9a4ad09-327a-4361-bee6-49d873f5215c
-- title:
--   Weight distribution $A_w(C)$ and truncated weight enumerator $W_q(C,d)$
-- statement:
--   Let $C\subseteq\mathbb F_Q^N$ be a linear code. For $w\ge 0$ the **weight distribution** counts the codewords of Hamming weight $w$,
--   $$
--   A_w(C)=|\{c\in C:\operatorname{wt}(c)=w\}|,
--   $$
--   and, for an integer $q$ and $d\ge 1$, the **truncated weight enumerator** is
--   $$
--   W_q(C,d)=\sum_{w=1}^{d-1}A_w(C)\left(\frac{q-1}{Q-1}\right)^w .
--   $$
--   $W_q(C,d)$ weighs each low-weight codeword by the probability $\bigl(\tfrac{q-1}{Q-1}\bigr)^w$ that a nonzero difference of weight $w$ survives a random restriction of every coordinate to $q$ of the $Q$ symbols (eq. (4.4)); Lemma 4.1 turns $W_q(C,d)\le 1$ into a $q$-ary code of distance $d$.
--
--   **Formalization Note** $\mathbb F_Q$ is a field `k` with $Q$ = `Nat.card k`; a linear code is a `Submodule k (Fin N → k)`; the weight is Mathlib's `hammingNorm`; $A_w$ is `weightDist` (a `Nat.card` of a subtype). The ratio $(q-1)/(Q-1)$ is a real division. The sum is over $w\in\{1,\dots,d-1\}$ and is empty for $d\le 1$. The paper's ranges $2\le q\le Q$ and $d\in[N+1]$ are hypotheses of the statements that use it.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4, eqs. (4.1)–(4.2), p.11 (PDF p.13)

import Mathlib

set_option autoImplicit false

namespace BeatingGV42

open Classical in
/-- **Weight distribution** `A_w(C) = |{c ∈ C : wt(c) = w}|` of a linear code `C ⊆ F_Q^N`
(Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4, eq. (4.1), p.11 (PDF p.13)).

**Formalization Note** `F_Q` is any field `k` (finite in every use, `Q = Nat.card k`), a linear
code is a `Submodule k (Fin N → k)`, and the weight is Mathlib's `hammingNorm` (number of nonzero
coordinates; decidability of equality in `k` is classical). The count is `Nat.card` of a subtype of
`C`, which is finite when `k` is. `A_0(C) = 1` for every `C`. -/
noncomputable def weightDist {k : Type*} [Field k] {N : ℕ} (C : Submodule k (Fin N → k)) (w : ℕ) :
    ℕ :=
  Nat.card {c : C // hammingNorm (c : Fin N → k) = w}

/-- **Truncated weight enumerator** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4, eq. (4.2), p.11 (PDF p.13)): for a linear code
`C ⊆ F_Q^N` and `d ∈ [N + 1]`,
`W_q(C, d) = Σ_{w=1}^{d−1} A_w(C) ((q − 1)/(Q − 1))^w`.

**Formalization Note** `Q = Nat.card k`; the ratio `(q − 1)/(Q − 1)` is a real division (not
`ℕ` division). The sum runs over `w ∈ Finset.Ico 1 d = {1, …, d − 1}` and is empty for `d ≤ 1`. The
paper uses `2 ≤ q ≤ Q` and `d ∈ [N + 1]`; those ranges are hypotheses of the statements, not of the
definition. -/
noncomputable def truncWE {k : Type*} [Field k] {N : ℕ} (q : ℕ) (C : Submodule k (Fin N → k))
    (d : ℕ) : ℝ :=
  ∑ w ∈ Finset.Ico 1 d,
    (weightDist C w : ℝ) * (((q : ℝ) - 1) / ((Nat.card k : ℝ) - 1)) ^ w

end BeatingGV42


