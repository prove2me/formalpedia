-- Prove2me | Definitions.Def_GyoriLovasz_IsShift
-- name    : GyoriLovasz_IsShift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:33.032089+00:00
-- url     : https://prove2.me/theorems/3d014cac-60c9-40df-ada1-6bf230ae37e6
-- title:
--   Directed cycle of the reassignment graph; shifting an assignment along it
-- statement:
--   Given labels $v_t$ ($t\in T$), the **reassignment graph** $\mathcal R$ on $T$ has, for each $t$, the edge $\varphi(v_t)\to t$ labeled $v_t$. A **directed cycle** $\mathcal C=(t_{i_1},\dots,t_{i_r},t_{i_1})$ of $\mathcal R$ is a list of distinct terminals with $\varphi(v_{i_j})=t_{i_{j-1}}$, indices modulo $r$. **Shifting** $\varphi$ along $\mathcal C$ gives
--   $$\varphi'(v)=\begin{cases}t_{i_j}&\text{if } v=v_{i_j}\text{ for some } j\in[r],\\ \varphi(v)&\text{otherwise.}\end{cases}$$
--
--   **Formalization Note** The shift is a relation between $\varphi$ and $\varphi'$ (it determines $\varphi'$ when it holds); that the labels on a cycle are distinct, so that a shift exists, is a clause of Lemma 4.12. A one-element list is a loop of $\mathcal R$.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), §4.1, p.25; Algorithm 3, lines 7–12, p.25

import Mathlib

namespace GyoriLovasz

/-- **A directed cycle of the reassignment graph `R`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), §4.1, p.25: `R` on `T` has, for each `t ∈ T`, the
edge `φ(v_t) → t` labeled by `v_t`, and "C = (t_{i_1}, t_{i_2}, ..., t_{i_r}, t_{i_1}) be such a cycle, where
indices are taken modulo r. For each j ∈ [r], the edge t_{i_{j−1}} → t_{i_j} is labeled by v_{i_j}, and
therefore φ(v_{i_j}) = t_{i_{j−1}}."

**Formalization Note.** `C` lists the terminals of the cycle once each. Consecutive entries give the edges of
the cycle, and the head and last entry give the closing edge. A one-element `C` is a loop of `R`;
`lemma_4_13` excludes it under the hypotheses of `lemma_4_12`. -/
def IsShiftCycle {V : Type*} (T : Finset V) (φ v : V → V) (C : List V) : Prop :=
  C.Nodup ∧ (∀ t ∈ C, t ∈ T) ∧ (C.IsChain fun a b => φ (v b) = a) ∧
    ∃ h : C ≠ [], φ (v (C.head h)) = C.getLast h

/-- **Shifting along a cycle.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), §4.1, p.25: "φ′(v) = t_{i_j} if v = v_{i_j} for some j ∈ [r], φ(v)
otherwise."

**Formalization Note.** A relation, so that no choice function is needed. It determines `φ′`. A separate
clause of `lemma_4_12` says such a `φ′` exists, that is, that the labels on a cycle are distinct. -/
def IsShift {V : Type*} (φ v : V → V) (C : List V) (φ' : V → V) : Prop :=
  (∀ t ∈ C, φ' (v t) = t) ∧ ∀ x, (∀ t ∈ C, x ≠ v t) → φ' x = φ x

end GyoriLovasz


