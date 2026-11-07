-- Prove2me | Definitions.Def_TwoFoldOPI_IsUnorderedPairPOVM
-- name    : TwoFoldOPI_IsUnorderedPairPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:20.258853+00:00
-- url     : https://prove2.me/theorems/190f38b5-6ec7-4e50-9660-510d1a9a40b4
-- title:
--   A measurement that outputs $\{c,c'\}$ with $c'$ uniform on $\mathbb F_q\setminus\{c\}$
-- statement:
--   A POVM $(E_s)$ on one qudit with outcomes the unordered pairs $s$ of field elements ($E_s\succeq0$, $\sum_sE_s=I$) has the behaviour of Lemma 7.2 if for every $c\in\mathbb F_q$ and every $s$,
--   $$\langle\phi_c|E_s|\phi_c\rangle=\begin{cases}\dfrac1{q-1},& s=\{c,c'\}\text{ with }c'\neq c,\\[2mm]0,&\text{otherwise},\end{cases}$$
--   where $|\phi_c\rangle=X^c\mathrm{QFT}^\dagger|A_i\rangle$. That is: on input $|\phi_c\rangle$ it outputs the pair $\{c,c'\}$ with $c'$ uniform on $\mathbb F_q\setminus\{c\}$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, Lemma 7.2, p. 38

import Mathlib
import Definitions.Def_TwoFoldOPI_singleInputState

open scoped Matrix ComplexOrder

namespace TwoFoldOPI

/-- **A measurement that outputs the unordered pair `{c, c′}` with `c′` uniform on `K ∖ {c}`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, Lemma 7.2, p.38: "there is a quantum measurement on a single F_q-qudit with the
following input-output behavior: when its input has the form X^c QFT†|A_i⟩ for some c ∈ F_q, it
outputs the unordered pair {c, c′} for uniformly random c′ ← F_q∖{c}."

`E` is a POVM with outcomes the unordered pairs `s ∈ Sym2 K` (each `E s` positive semidefinite,
`Σ_s E s = 1`), and for every `c` and `s`, outcome `s` has probability
`⟨ϕ_c|E_s|ϕ_c⟩ = 1/(q − 1)` if `s = {c, c′}` with `c′ ≠ c`, and `0` otherwise, where
`ϕ_c = X^c QFT† |K ∖ {β}⟩`.

**Formalization Note.** "`s = {c, c′}` with `c′ ≠ c`" is `c ∈ s ∧ ¬ s.IsDiag`. The probabilities
are stated as complex numbers `star ϕ ⬝ᵥ (E s *ᵥ ϕ)`. -/
def IsUnorderedPairPOVM (F : AvgCaseTI.FieldPres) (β : F.F)
    (E : Sym2 F.F → Matrix (Fin 1 → F.F) (Fin 1 → F.F) ℂ) : Prop :=
  (∀ s, (E s).PosSemidef) ∧ ∑ s, E s = 1 ∧
    ∀ (c : F.F) (s : Sym2 F.F),
      star (WithLp.ofLp (singleInputState F β c)) ⬝ᵥ
          (E s *ᵥ WithLp.ofLp (singleInputState F β c)) =
        if c ∈ s ∧ ¬ s.IsDiag then ((Fintype.card F.F : ℂ) - 1)⁻¹ else 0

end TwoFoldOPI


