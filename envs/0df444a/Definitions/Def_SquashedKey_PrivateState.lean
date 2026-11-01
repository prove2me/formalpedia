-- Prove2me | Definitions.Def_SquashedKey_PrivateState
-- name    : SquashedKey_PrivateState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:32:04.197374+00:00
-- url     : https://prove2.me/theorems/70e62814-e3f9-4953-9909-580cabdcf02c
-- title:
--   Private states: the key readout $(\mathcal M_A\otimes\mathcal M_B\otimes\mathrm{Tr}_{A'B'})\varphi$ and definition (5)
-- statement:
--   Let $\gamma_{ABA'B'}$ be a state with key systems $A$, $B$ of dimension $K<+\infty$ and shields $A'$, $B'$ of arbitrary dimension. Let $\mathcal M(\cdot)=\sum_i |i\rangle\langle i|(\cdot)|i\rangle\langle i|$ be the measurement channel in the standard basis.
--
--   **Key readout.** For a unit vector $|\varphi\rangle_{ABA'B'E}$, the operator $(\mathcal M_A\otimes\mathcal M_B\otimes\operatorname{Tr}_{A'B'})(\varphi)$ on $ABE$ has matrix elements
--   $$
--   \langle a,b,e|\cdot|a',b',e'\rangle=\delta_{aa'}\delta_{bb'}\sum_{s,t}\varphi(a,s,b,t,e)\,\overline{\varphi(a,s,b,t,e')} .
--   $$
--
--   **Private state ((5), p.4).** $\gamma$ is a private state of $\log_2 K$ private bits if, for any purification $|\varphi^\gamma\rangle_{ABA'B'E}$ of $\gamma$ (on any purifying system $E$),
--   $$
--   (\mathcal M_A\otimes\mathcal M_B\otimes\operatorname{Tr}_{A'B'})(\varphi^\gamma_{ABA'B'E})=\frac1K\sum_i |i\rangle\langle i|_A\otimes|i\rangle\langle i|_B\otimes\sigma_E
--   $$
--   for some state $\sigma_E$, which may depend on the purification.
--
--   This is the class of states for which Theorem 2 bounds $\log_2 K$ by the squashed entanglement of any nearby state.
--
--   **Formalization Note** The state lives on $(A A')(B B')$ with index $((a,s),(b,t))$, key systems $\{0,\dots,K-1\}$, shields arbitrary types. "Any purification" ranges over every type $E$ and every unit vector $\varphi\in\ell^2$ of the five registers whose partial trace over $E$ is $\gamma$. The definition is (5) itself; the twisted form (6) is a theorem of the mission.
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, §2.3, definition (5), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_SquashedKey_FiveParty

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceSecond)

namespace SquashedKey

/-- **Key readout of a purification**, Wilde, *Squashed entanglement and approximate private
states*, arXiv:1606.08028v3, §2.3, (5), p.4 (PDF p.4): the operator
`(M_A ⊗ M_B ⊗ Tr_{A′B′}) φ_{ABA′B′E}` obtained from the pure state `φ = |φ⟩⟨φ|` by measuring the key
systems `A` and `B` in the standard basis, `M(·) = Σᵢ |i⟩⟨i|(·)|i⟩⟨i|`, and tracing out the shields
`A′B′`. Its coefficient at `((a, b), e), ((a′, b′), e′)` is
`δ_{aa′} δ_{bb′} Σ_{s,t} φ(((a,s),(b,t)),e) · conj φ(((a,s),(b,t)),e′)`.

**Formalization Note** `φ ∈ ℓ²(((Fin K × A′) × (Fin K × B′)) × E)`; the result is an operator on
`(A B) E` with index `((a, b), e)`. The sum over the shield indices converges absolutely for
`φ ∈ ℓ²` (Cauchy–Schwarz). -/
noncomputable def keyReadout {K : ℕ} {A' B' E : Type} (φ : Hilbert (FiveParty K A' B' E)) :
    Matrix ((Fin K × Fin K) × E) ((Fin K × Fin K) × E) ℂ :=
  fun p q => if p.1 = q.1 then
    ∑' st : A' × B', φ (((p.1.1, st.1), (p.1.2, st.2)), p.2) *
      star (φ (((p.1.1, st.1), (p.1.2, st.2)), q.2))
  else 0

/-- **Private state**, arXiv:1606.08028v3, §2.3, (5), p.4 (PDF p.4). A state `γ_{ABA′B′}` with
key systems of dimension `K = dim H_A = dim H_B < +∞` "is a private state of `log₂ K` private bits
if, for any purification `|φ^γ⟩_{ABA′B′E}` of `γ_{ABA′B′}`, the following holds:
`(M_A ⊗ M_B ⊗ Tr_{A′B′}) φ^γ_{ABA′B′E} = (1/K) Σᵢ |i⟩⟨i|_A ⊗ |i⟩⟨i|_B ⊗ σ_E`, (5)
where `M(·) = Σᵢ |i⟩⟨i|(·)|i⟩⟨i|` is a projective measurement channel and `σ_E` is some state on the
purifying system `E` (which could depend on the particular purification)."

**Formalization Note** The state lives on `(Fin K × A′) × (Fin K × B′)` (Alice's `AA′`, Bob's
`BB′`); the shields `A′`, `B′` are arbitrary types (any dimension, infinite included). "Any
purification" ranges over every purifying system `E : Type` and every unit vector
`φ ∈ ℓ²(((Fin K × A′) × (Fin K × B′)) × E)` with `Tr_E |φ⟩⟨φ| = γ`. The right-hand side of (5) has
coefficient `(1/K) σ_E(e, e′)` at `((a, b), e), ((a′, b′), e′)` when `a = a′ = b = b′`, and `0`
otherwise. This is the paper's defining property (5); the twisted form (6) is a consequence,
stated as a theorem of the mission. -/
def IsPrivateState {K : ℕ} {A' B' : Type} (γ : State ((Fin K × A') × (Fin K × B'))) : Prop :=
  ∀ (E : Type) (φ : Hilbert (FiveParty K A' B' E)), ‖φ‖ = 1 →
    partialTraceSecond (rankOne φ) = γ.coefficients →
    ∃ σ : State E, keyReadout φ = fun p q =>
      if p.1 = q.1 ∧ p.1.1 = p.1.2 then (K : ℂ)⁻¹ * σ.coefficients p.2 q.2 else 0

end SquashedKey


