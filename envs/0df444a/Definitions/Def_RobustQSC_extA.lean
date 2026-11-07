-- Prove2me | Definitions.Def_RobustQSC_extA
-- name    : RobustQSC_extA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:40.000543+00:00
-- url     : https://prove2.me/theorems/03f55a02-8afa-46c6-b971-faca52c0e99c
-- title:
--   The extension operator $\mathrm{Ext}_A$
-- statement:
--   For $A\subseteq\{0,1\}^n$ and $h:\{0,1\}^n\to\mathbb C$,
--
--   $$
--   (\mathrm{Ext}_Ah)(x)=\begin{cases}h(x),&x\in A,\\ \dfrac1{|N_A(b)|}\displaystyle\sum_{u\in N_A(b)}h(u),&x=b\notin A,\end{cases}
--   $$
--
--   where $N_A(b)=\{x\in A:x\sim b\}$ is the set of neighbours of $b$ in $A$.
--
--   **Formalization Note** If $N_A(b)=\emptyset$ the value is $0$ in Lean; the local escape property, under which $\mathrm{Ext}_A$ is used, excludes this for $n\ge1$.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §6, p.48

import Definitions.Def_QAlgorithms_Defs_Basic

namespace RobustQSC

open QAlgorithms

/-- The extension operator `Ext_A`: `(Ext_A h)(x) = h(x)` for `x ∈ A`, and for `b ∉ A` the
average of `h` over `N_A(b) = {x ∈ A : x ∼ b}`, the neighbours of `b` in `A`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §6, p.48 (display defining `Ext_A`).

**Formalization Note.** `x ∼ b` is Hamming distance `1`. If `N_A(b) = ∅` the value is `0`
(Lean's `a/0 = 0`); the local escape property, under which `Ext_A` is used, rules this out. -/
noncomputable def extA {n : ℕ} (A : Set (Qubits n)) (h : Qubits n → ℂ) : Qubits n → ℂ := by
  classical
  exact fun b => if b ∈ A then h b else
    (∑ x ∈ Finset.univ.filter (fun x => x ∈ A ∧ hammingDist x b = 1), h x) /
      ((Finset.univ.filter (fun x => x ∈ A ∧ hammingDist x b = 1)).card : ℂ)

end RobustQSC


