-- Prove2me | Definitions.Def_CompNonlocal_Certificate_align
-- name    : CompNonlocal_Certificate_align
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:39.689101+00:00
-- url     : https://prove2.me/theorems/996a23d3-5f83-4aa8-ba44-6f09a7539734
-- title:
--   The alignment $\mathfrak a$
-- statement:
--   With Alice's effects $E_{x,a}=p_x(a)(I+n_{x,a}\cdot\sigma)$, $r(x,a):=-n_{x,a}$, and $W_{x,a}=w^0_{x,a}I+w_{x,a}\cdot\sigma$,
--   $$\mathfrak a:=\mathbb E[\langle w_{x,a},r(t)\rangle]=\sum_x\Pr[x]\sum_a p_x(a)\,\langle w_{x,a},r(x,a)\rangle .$$
--   It measures how well the test's sensitivity to Bob's Bloch direction aligns with the conditional state; honest acceptance on $\rho(u)$ is $h_u=\mathfrak b+u\,\mathfrak a$ (Lemma 9).
--
--   **Formalization Note** Written with the normalizations multiplied out; zero effects contribute $0$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §6.3, p.30 and Definition 13, p.31

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_bobAccEffect
import Definitions.Def_CompNonlocal_blochVec

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The alignment `𝔞` of a certificate at security parameter `κ`. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), §6.3, p.30 ("Write Alice's nonzero POVM effects as
E_{x,a} = p_x(a)(I + n_{x,a} · σ), p_x(a) := ½ Tr(E_{x,a}) … and set r(t) := −n_{x,a} for t = (x, a)")
and Definition 13, p.31 ("𝔞 := E[⟨w_{x,a}, r(t)⟩]", with `W_{x,a} = w⁰_{x,a} I + w_{x,a} · σ`).

**Formalization Note** `𝔞 = Σ_x Pr[x] Σ_a p_x(a) ⟨w_{x,a}, r(x, a)⟩`, with the conditioning and the
normalizations multiplied out: `p_x(a) r(x, a) = −½ blochVec(E_{x,a})` and
`Pr[x] w_{x,a} = ½ Σ_{o ↦ x} blochVec(bobAccEffect o a)`. Zero effects (`p_x(a) = 0`) contribute `0`,
as in the paper, where `r` is defined only for nonzero effects. -/
noncomputable def Certificate.align (c : Certificate) (κ : ℕ) : ℝ :=
  ∑ o : Bits (c.Qg κ).outC.length, ∑ a : Bits (c.A κ).outC.length, ∑ j : Fin 3,
    -((blochVec ((c.A κ).qubitEffect ((List.ofFn o).take (c.lx κ))
          (fun t => decide (t = List.ofFn a)))) j / 2) *
      ((blochVec (c.bobAccEffect κ (List.ofFn o) (List.ofFn a))) j / 2)

end CompNonlocal


