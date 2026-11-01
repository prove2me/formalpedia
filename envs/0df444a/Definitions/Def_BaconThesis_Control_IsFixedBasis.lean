-- Prove2me | Definitions.Def_BaconThesis_Control_IsFixedBasis
-- name    : BaconThesis_Control_IsFixedBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:07.089223+00:00
-- url     : https://prove2.me/theorems/ab160f7b-ae81-4af0-b908-ca35a6b4890f
-- title:
--   Fixed Hermitian operator basis $F_0 = I/\sqrt d,\ F_\alpha$ traceless, $\mathrm{Tr}[F_\alpha^\dagger F_\beta] = \delta_{\alpha\beta}$
-- statement:
--   Let $\mathcal H_S = \mathbb C^s$ be a Hilbert space of dimension $d = |s|$. A family $(F_\alpha)_{\alpha\in\kappa}$ of operators on $\mathcal H_S$, indexed by a finite set $\kappa$ with a distinguished index $0$, is a **fixed basis** when
--
--   1. every $F_\alpha$ is Hermitian;
--   2. $F_0 = \frac{1}{\sqrt d}\, I$;
--   3. every $F_\alpha$ with $\alpha \neq 0$ is traceless;
--   4. the family is trace orthonormal,
--   $$
--   \mathrm{Tr}\big[F_\alpha^\dagger F_\beta\big] = \delta_{\alpha\beta};
--   $$
--   5. complex linear combinations of the $F_\alpha$ give every operator on $\mathcal H_S$.
--
--   This is the basis over which the system-apparatus Hamiltonian is expanded in the stationary control conditions; for a qubit the normalized Pauli matrices $\sigma_\alpha/\sqrt 2$ are one.
--
--   **Formalization Note** The index set is any finite type with a distinguished element. The book's range $\alpha = 1,\dots,2d^2-1$ is a misprint for $d^2 - 1$, which follows from 4 and 5. Clause 3 follows from 2 and 4 and is kept because the book states it; the book's remark that real combinations span the Hermitian operators follows from 1 and 5. No fixed basis exists for $d = 0$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Appendix A.3 "Fixed basis formalism", eq. (A.3), p.231 (PDF p.248); used in §3.2.1, eq. (3.3), p.32 (PDF p.49)

import Mathlib

open scoped Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
Appendix A.3 "Fixed basis formalism", eq. (A.3), p.231 (PDF p.248), used in §3.2.1, eq. (3.3),
p.32 (PDF p.49): a **fixed basis** of the operators on a `d`-dimensional Hilbert space `ℂ^s` is a
family `F : κ → Matrix s s ℂ` with a distinguished index `i0` (the book's `α = 0`) such that

1. every `F α` is Hermitian;
2. `F i0 = (1/√d) I`, with `d = card s`;
3. every `F α` with `α ≠ i0` is traceless;
4. the family is trace orthonormal, `Tr[F_α† F_β] = δ_{αβ}` (A.3);
5. the `F α` span all operators on `ℂ^s` over `ℂ`.

**Formalization Note.** The index set is any finite type `κ` with a distinguished element `i0`
(the book numbers the indices `0, 1, …`; its upper limit `2d² − 1` is a misprint for `d² − 1`, which
follows from 4 and 5). Clause 3 is implied by 2 and 4 and is kept because the book states it.
The book's further remark that real combinations span the Hermitian operators follows from 1
and 5. For an empty `s` clause 4 fails at `α = β = i0`, so a fixed basis exists only for `d ≥ 1`. -/
def IsFixedBasis {s κ : Type} [Fintype s] [DecidableEq s] [DecidableEq κ]
    (F : κ → Matrix s s ℂ) (i0 : κ) : Prop :=
  (∀ α, (F α).IsHermitian) ∧
  F i0 = ((Real.sqrt (Fintype.card s) : ℂ))⁻¹ • (1 : Matrix s s ℂ) ∧
  (∀ α, α ≠ i0 → (F α).trace = 0) ∧
  (∀ α β, ((F α)ᴴ * F β).trace = if α = β then 1 else 0) ∧
  Submodule.span ℂ (Set.range F) = ⊤

end BaconThesis.Control


