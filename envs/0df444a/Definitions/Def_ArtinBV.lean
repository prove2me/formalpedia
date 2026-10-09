-- Prove2me | Definitions.Def_ArtinBV
-- name    : ArtinBV
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T16:41:47.345981+00:00
-- url     : https://prove2.me/theorems/83645d5b-b2ea-4509-b7e8-b0992a85c88f
-- title:
--   Chebyshev functions of progressions and characters, primitive characters, truncations (for the Bombieri–Vinogradov theorem)
-- statement:
--   Definitions used by the steps of the proof of the Bombieri–Vinogradov theorem, which OpenAI's *Primitive roots for every admissible integer base* (2026) applies at (12.16), p. 77. Here $\Lambda$ is Mathlib's von Mangoldt function `ArithmeticFunction.vonMangoldt`.
--
--   - `psiAP X q a`: $\psi(X; q, a) = \sum_{0 < n \le X,\ n \equiv a \ (\mathrm{mod}\ q)} \Lambda(n)$, for natural numbers $X, q, a$.
--   - `psiChar χ X`: $\psi(X, \chi) = \sum_{0 < n \le X} \Lambda(n)\chi(n)$, for a Dirichlet character `χ : DirichletCharacter ℂ d` and a natural number $X$.
--   - `primChars d`: the finite set of primitive Dirichlet characters modulo $d$, that is, those whose conductor (Mathlib's `DirichletCharacter.conductor`) equals $d$. For $d = 1$ it contains the trivial character.
--   - `trunc f U`: the truncation $n \mapsto f(n)\,\mathbf 1_{n \le U}$ of a real arithmetic function $f$, again an `ArithmeticFunction ℝ`. In Vaughan's identity it gives $\Lambda_V = $ `trunc Λ V` and $\mu_U = $ `trunc μ U`.
--
--   These are standard objects (Davenport, *Multiplicative Number Theory*, ch. 17, 24, 28). The bundle contains definitions only.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, step of the proof of the Bombieri–Vinogradov theorem (12.16)

import Mathlib

namespace ArtinPrimitiveRoots

open ArithmeticFunction Finset

/-- The Chebyshev function of a residue class, `ψ(X; q, a) = ∑_{n ≤ X, n ≡ a (mod q)} Λ(n)`. -/
noncomputable def psiAP (X q a : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 X).filter (fun n => n ≡ a [MOD q]), Λ n

/-- The twisted Chebyshev function `ψ(X, χ) = ∑_{n ≤ X} Λ(n) χ(n)` of a Dirichlet character `χ`. -/
noncomputable def psiChar {d : ℕ} (χ : DirichletCharacter ℂ d) (X : ℕ) : ℂ :=
  ∑ n ∈ Ioc 0 X, (Λ n : ℂ) * χ n

/-- The primitive Dirichlet characters modulo `d` (those of conductor `d`). -/
noncomputable def primChars (d : ℕ) : Finset (DirichletCharacter ℂ d) :=
  univ.filter (fun χ => χ.conductor = d)

/-- The truncation `n ↦ f(n) 1_{n ≤ U}` of an arithmetic function `f`. -/
noncomputable def trunc (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

end ArtinPrimitiveRoots


