-- Prove2me | Definitions.Def_LocalSweepFT_failProb
-- name    : LocalSweepFT_failProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:44:44.849275+00:00
-- url     : https://prove2.me/theorems/a1679da8-e0f1-45d8-a236-450560418c3f
-- title:
--   Referees, decoding to the logical space, local stochastic noise, and the failure probability
-- statement:
--   A **referee** for the nice encoding is a quantum channel $D$ (Choi–Kraus form) from one register to one qubit with $D(\mathrm{Enc}\,\rho\,\mathrm{Enc}^\dagger)=\rho$ for every one-qubit $\rho$. Given an injective map $\mathrm{out}$ from the $w$ qubits of $C$ to the registers of $\tilde C$, **decoding** a state of $\tilde C$ traces out every other wire and applies $D$ to each register $\mathrm{out}(j)$.
--
--   A distribution $\nu$ on fault patterns is **local stochastic of rate $p$** if for every finite set $S$ of locations
--   $$\Pr_{E\sim\nu}\big[E_\ell\ne I\ \text{for every }\ell\in S\big]\le p^{|S|}.$$
--   The **failure probability** of $\tilde C$ as a simulation of $C$ is $\Pr_{E\sim\nu}[\text{decoded }\tilde C[E]\ne C(|0^w\rangle\langle0^w|)]$.
--
--   These objects state Def. 6.1 and the conclusion of Lemma 6.2 and Theorem 6.3.
--
--   **Formalization Note** The failure event is exact inequality of the decoded output, the event bounded in the proof of Lemma 6.2 (p.58). The referee uses the platform's quantum channel `WildeQIT.QChannel`, which carries its trace-preservation condition.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definition 6.1, pp.56–57; Definition 3.7, p.14

import Mathlib
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_LocalSweepFT_liftOn
import Definitions.Def_LocalSweepFT_encMat
import Definitions.Def_LocalSweepFT_IdealCircuit
import Definitions.Def_LocalSweepFT_ToricEncodedCircuit

open Matrix

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…): referees and simulation (Def 6.1, pp.56–57) and local
stochastic noise (Def 3.7, p.14). -/

variable {d d' n : ℕ} [NeZero n]

/-- A referee for the nice encoding with direction set `S′` (Def 6.1, p.56): a quantum channel
(Choi–Kraus form, `WildeQIT.QChannel`) from one register to one qubit that returns the logical
state of every encoded state: `D(Enc ρ Enc†) = ρ` for every one-qubit operator `ρ`. -/
def IsReferee (S : DirSet d d')
    (D : WildeQIT.QChannel (QCell d d' n → ZMod 2) (Fin 1 → ZMod 2)) : Prop :=
  ∀ ρ : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ,
    D.apply (encMat S * ρ * (encMat S).conjTranspose) = ρ

open Classical in
/-- Decoding the registers back to the logical space (Def 6.1 (1)): trace out every wire that is
not in one of the registers `out 0, …, out (w−1)` (classical bits included) and apply the referee
`D` to each register `out j`, giving a `w`-qubit operator whose qubit `j` comes from register
`out j`. -/
noncomputable def decodeOut {R nb w : ℕ}
    (D : WildeQIT.QChannel (QCell d d' n → ZMod 2) (Fin 1 → ZMod 2)) (out : Fin w ↪ Fin R)
    (ρ : Op (Wire R nb d d' n)) : Op (Fin w) :=
  let kept : Wire R nb d d' n → Prop := fun x => ∃ j q, x = Sum.inl (out j, q)
  let K : (Fin w → D.ι) → ({x // ¬ kept x} → ZMod 2) →
      Matrix (Fin w → ZMod 2) (Wire R nb d d' n → ZMod 2) ℂ :=
    fun i e y a => (if ∀ x : {x // ¬ kept x}, a x.1 = e x then 1 else 0) *
      ∏ j, D.K (i j) (fun _ => y j) (fun q => a (Sum.inl (out j, q)))
  ∑ i, ∑ e, K i e * ρ * (K i e).conjTranspose

/-- A noise channel `N_E` (a distribution `ν` on fault patterns of `C̃`) is local stochastic with
rate `p` (Def 3.7, p.14): for every finite set `S` of locations, the probability that every
location of `S` carries a non-identity Pauli fault is at most `p^{|S|}`. -/
def IsLocalStochastic (C : ToricEncodedCircuit d d' n) (ν : PMF (FaultPattern C)) (p : ℝ) : Prop :=
  ∀ S : Finset (Fin C.depth × (Fin C.R × QCell d d' n)),
    ν.toOuterMeasure {E | ∀ l ∈ S, E l.1 l.2 ≠ 0} ≤ ENNReal.ofReal (p ^ S.card)

/-- The failure probability of `C̃` as a simulation of `C` (Def 6.1 (2), read semantically): the
probability under `ν` of a fault pattern `E` for which decoding the registers `out j` of the noisy
run `C̃[E]` (sweep rules `rule₁`, `rule₂`) does not give exactly the output `C(|0^w⟩⟨0^w|)`. -/
noncomputable def failProb {w μ : ℕ} (hd : d' ≤ d) (rule₁ : LocalRule d d')
    (rule₂ : LocalRule d (d - d')) (C : IdealCircuit w μ) (Ct : ToricEncodedCircuit d d' n)
    (D : WildeQIT.QChannel (QCell d d' n → ZMod 2) (Fin 1 → ZMod 2)) (out : Fin w ↪ Fin Ct.R)
    (ν : PMF (FaultPattern Ct)) : ENNReal :=
  ν.toOuterMeasure {E | decodeOut D out (run hd rule₁ rule₂ Ct E) ≠ idealOut C}

end LocalSweepFT


