-- Prove2me | Definitions.Def_SharpConsist_fref
-- name    : SharpConsist_fref
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:52.630199+00:00
-- url     : https://prove2.me/theorems/32d27e63-d2bb-484c-933f-2495cf144450
-- title:
--   The reference instance $f_{\mathrm{ref}}$ of Eq. (5.10)
-- statement:
--   On $X\cup\{r\}$ with $X=[n]$, the **reference instance** is
--   $$f_{\mathrm{ref}}(U)=\psi\Bigl(\frac{|U\cap X|}{k}\Bigr).$$
--   Its answers to queries $S\subseteq X$ depend only on $|S|$, and they coincide with those of $f_A$ on every balanced set $|u_A(S)|\le\delta$; it is used to run an algorithm against answers that do not depend on the hidden set.
--
--   **Formalization Note.** $X\cup\{r\}$ is `Fin (n+1)`, $X$ the image of `Fin n`, $r$ = `Fin.last n`.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Eq. (5.10), p.15

import Mathlib
import Definitions.Def_SharpConsist_psi
import Definitions.Def_SharpConsist_embedX

namespace SharpConsist

/-- The **reference instance** of Eq. (5.10): `f_ref(U) = ψ(|U ∩ X|/k)` on `X ∪ {r}`. Fu–Zhang–Tao,
arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, p.15.

**Formalization Note.** `X ∪ {r} = Fin (n+1)`, `X = embedX univ` (the image of `Fin n`), `r = Fin.last n`. -/
noncomputable def fref (T : ℝ) (m k : ℕ) {n : ℕ} (U : Finset (Fin (n + 1))) : ℝ :=
  psi T m (((U ∩ embedX (Finset.univ : Finset (Fin n))).card : ℝ) / (k : ℝ))

end SharpConsist


