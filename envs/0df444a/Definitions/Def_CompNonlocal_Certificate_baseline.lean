-- Prove2me | Definitions.Def_CompNonlocal_Certificate_baseline
-- name    : CompNonlocal_Certificate_baseline
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:50.238095+00:00
-- url     : https://prove2.me/theorems/1f000938-bcc0-4b38-b780-d17b3f5f1cd6
-- title:
--   The baseline $\mathfrak b$
-- statement:
--   With $W_{x,a}=w^0_{x,a}I+w_{x,a}\cdot\sigma$ (Eq. (18)) and $p_x(a)=\frac12\operatorname{Tr}E_{x,a}$ the probability of Alice's answer,
--   $$\mathfrak b:=\mathbb E[w^0_{x,a}]=\sum_x\Pr[x]\sum_a p_x(a)\,w^0_{x,a}.$$
--
--   **Formalization Note** Written with the conditioning on $x$ multiplied out (no division).
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 13, p.31

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_bobAccEffect

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The baseline `𝔟` of a certificate at security parameter `κ`. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), Definition 13, p.31: with `W_{x,a} = w⁰_{x,a} I + w_{x,a} · σ`
(Eq. (18)), "expectations are over the generated question X and a ← p_X … Set 𝔟 := E[w⁰_{x,a}]",
where `p_x(a) := ½ Tr(E_{x,a})` is the probability of Alice's answer `a` on `x` (§6.3, p.30).

**Formalization Note** `𝔟 = Σ_x Pr[x] Σ_a p_x(a) w⁰_{x,a}`, written with the conditioning on `x`
multiplied out: `Σ_o Σ_a p_{x(o)}(a) · ½ Tr(bobAccEffect o a)`, where `o` ranges over the question
outcomes and `a` over Alice's answers. -/
noncomputable def Certificate.baseline (c : Certificate) (κ : ℕ) : ℝ :=
  ∑ o : Bits (c.Qg κ).outC.length, ∑ a : Bits (c.A κ).outC.length,
    (((c.A κ).qubitEffect ((List.ofFn o).take (c.lx κ)) (fun t => decide (t = List.ofFn a))).trace.re
        / 2) *
      ((c.bobAccEffect κ (List.ofFn o) (List.ofFn a)).trace.re / 2)

end CompNonlocal


