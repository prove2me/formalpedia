-- Prove2me | Definitions.Def_SquashedKey_Twisting
-- name    : SquashedKey_Twisting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:31:17.868375+00:00
-- url     : https://prove2.me/theorems/c28ed5fb-cf37-4c1e-ab15-d660111263b2
-- title:
--   Twisting unitaries and the twisted forms $U(\Phi\otimes\sigma)U^\dagger$ of (6) and (9)
-- statement:
--   **Twisting unitary ((8), p.4).** A family $(U^{ij}_{A'B'})_{i,j=0}^{K-1}$ of unitaries on $H_{A'B'}$ defines the controlled unitary
--   $$
--   U_{ABA'B'}=\sum_{i,j}|i\rangle\langle i|_A\otimes|j\rangle\langle j|_B\otimes U^{ij}_{A'B'} .
--   $$
--
--   **Twisted state ((6)–(7), p.4).** With $\Phi_{AB}=\frac1K\sum_{i,j}|i\rangle\langle j|_A\otimes|i\rangle\langle j|_B$ and a state $\sigma_{A'B'}$, the operator $U(\Phi_{AB}\otimes\sigma_{A'B'})U^\dagger$ has blocks
--   $$
--   \langle a,b|\,U(\Phi\otimes\sigma)U^\dagger\,|a',b'\rangle=\delta_{ab}\,\delta_{a'b'}\,\frac1K\,U^{aa}\sigma\,(U^{a'a'})^\dagger .
--   $$
--
--   **Twisted extension ((9), p.4; (35), p.8).** For an operator $\sigma_{A'B'E}$, $(U\otimes 1_E)(\Phi\otimes\sigma_{A'B'E})(U\otimes 1_E)^\dagger$ has the same block form with $\sigma$ replaced by $\sigma_{A'B'E}$ and $U^{ii}$ by $U^{ii}\otimes 1_E$.
--
--   These forms describe private states (6) and their extensions (9), which drive the proof of Lemma 1.
--
--   **Formalization Note** Unitaries are elements of the unitary group of bounded operators on $\ell^2(A'\times B')$. The block $U\sigma V^\dagger$ is computed as a genuine operator product of the bounded realization of $\sigma$ (published `Frontier18_P18`), read back as a coefficient array; for an extension, block by block in $E$.
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, §2.3, (6)–(9), p.4; (35), p.8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_SquashedKey_FiveParty

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

namespace SquashedKey

/-- **Two-sided unitary conjugation of a block**, arXiv:1606.08028v3, (35)–(37), p.8: the
coefficient array of `U X V†` for bounded operators `U, V` on `ℓ²(J)` and a trace-class array `X`.

**Formalization Note** `boundedOperator X` is the bounded operator with coefficient array `X` and
`operatorCoeff` reads off the coefficients `⟨j|·|j′⟩` of a bounded operator (published bundle
`Frontier18_P18`); the composition is a genuine operator product. -/
noncomputable def twistBlock {J : Type} (U V : Hilbert J →L[ℂ] Hilbert J) (X : Matrix J J ℂ) :
    Matrix J J ℂ :=
  operatorCoeff (U.comp ((boundedOperator X).comp (ContinuousLinearMap.adjoint V)))

/-- **Twisting unitary data**, arXiv:1606.08028v3, (8), p.4: a family `(U^{ij}_{A′B′})_{i,j}` of
unitary operators on `H_{A′B′} = ℓ²(A′ × B′)`, indexed by the key values `i` of `A` and `j` of `B`.
The twisting unitary is the controlled unitary `U = Σ_{i,j} |i⟩⟨i|_A ⊗ |j⟩⟨j|_B ⊗ U^{ij}_{A′B′}`. -/
abbrev TwistingUnitary (K : ℕ) (A' B' : Type) :=
  Fin K → Fin K → unitary (Hilbert (A' × B') →L[ℂ] Hilbert (A' × B'))

/-- **Twisted form of a private state**, arXiv:1606.08028v3, (6)–(8), p.4:
`U_{ABA′B′} (Φ_{AB} ⊗ σ_{A′B′}) U†_{ABA′B′}`, with `Φ_{AB} = (1/K) Σ_{i,j} |i⟩⟨j|_A ⊗ |i⟩⟨j|_B` (7)
and `U` the controlled unitary (8). Its coefficient at `((a, s), (b, t)), ((a′, s′), (b′, t′))` is
`(1/K) (U^{aa} σ (U^{a′a′})†)((s, t), (s′, t′))` when `a = b` and `a′ = b′`, and `0` otherwise
(only the diagonal blocks `U^{ii}` act, since `Φ` is supported on `|ii⟩`; cf. (35), p.8).

**Formalization Note** Registers are ordered `(A A′)(B B′)`, i.e. index `((a, s), (b, t))`, rather
than the paper's `ABA′B′`; `σ` is an operator on `A′ × B′` with index `(s, t)`. -/
noncomputable def twistedState {K : ℕ} {A' B' : Type} (σ : Matrix (A' × B') (A' × B') ℂ)
    (U : TwistingUnitary K A' B') :
    Matrix ((Fin K × A') × (Fin K × B')) ((Fin K × A') × (Fin K × B')) ℂ :=
  fun p q => if p.1.1 = p.2.1 ∧ q.1.1 = q.2.1 then
    (K : ℂ)⁻¹ * twistBlock (U p.1.1 p.1.1 : Hilbert (A' × B') →L[ℂ] Hilbert (A' × B'))
      (U q.1.1 q.1.1 : Hilbert (A' × B') →L[ℂ] Hilbert (A' × B')) σ (p.1.2, p.2.2) (q.1.2, q.2.2)
  else 0

/-- **Twisted form of an extension**, arXiv:1606.08028v3, (9), p.4, and (35), p.8:
`U_{AA′BB′} (Φ_{AB} ⊗ σ_{A′B′E}) U†_{AA′BB′}`, with `U` acting as the identity on `E`. Its
coefficient at `(((a, s), (b, t)), e), (((a′, s′), (b′, t′)), e′)` is
`(1/K) (U^{aa} σ_{ee′} (U^{a′a′})†)((s, t), (s′, t′))` when `a = b` and `a′ = b′`, and `0`
otherwise, where `σ_{ee′}` is the `(e, e′)` block of `σ_{A′B′E}`, the operator on `A′B′` with
coefficients `σ_{A′B′E}(((s, t), e), ((s′, t′), e′))`.

**Formalization Note** `(U ⊗ 1_E) σ (V ⊗ 1_E)†` has `(e, e′)` block `U σ_{ee′} V†`; this is the
formula (35) entrywise in `E`. -/
noncomputable def twistedExtension {K : ℕ} {A' B' E : Type}
    (σE : Matrix ((A' × B') × E) ((A' × B') × E) ℂ) (U : TwistingUnitary K A' B') :
    Matrix (FiveParty K A' B' E) (FiveParty K A' B' E) ℂ :=
  fun p q => if p.1.1.1 = p.1.2.1 ∧ q.1.1.1 = q.1.2.1 then
    (K : ℂ)⁻¹ * twistBlock (U p.1.1.1 p.1.1.1 : Hilbert (A' × B') →L[ℂ] Hilbert (A' × B'))
      (U q.1.1.1 q.1.1.1 : Hilbert (A' × B') →L[ℂ] Hilbert (A' × B'))
      (fun x y => σE (x, p.2) (y, q.2)) (p.1.1.2, p.1.2.2) (q.1.1.2, q.1.2.2)
  else 0

end SquashedKey


