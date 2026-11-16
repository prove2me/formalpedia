-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_extLocality
-- name    : AutoQMem_Lindblad_Supplement_extLocality
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:46:40.633207+00:00
-- url     : https://prove2.me/theorems/32eea7d5-1096-485e-ad91-46a817cf0bc3
-- title:
--   Geometric locality, periodicity and equivariance of a register-extended Lindbladian
-- statement:
--   An operator on $\mathcal H^{\mathrm{ext}}$ is **supported** on a set of data qubits $S$ and registers $T$ if it is $O'\otimes I$ with $O'$ acting on $S\cup T$. A register-extended syndrome-based Lindbladian is **$R$-local** if every jump with site label $i$ is supported on $N_R(i)$ together with the registers located there, and $H(t)=\sum_iH_i(t)$ with each $H_i(t)\in\mathcal A^{\mathrm{ext}}$ Hermitian and supported in the same region. Distances are in the interaction graph of the CSS code, and registers count as located at their site. It is **periodic with period $\Delta$** if $H(t+\Delta)=H(t)$ and $f_\alpha(t+\Delta)=f_\alpha(t)$ for $t\ge0$.
--
--   It is **equivariant** under the symmetries of the code pair and two update rules if the following holds. For every permutation $\pi_s$ of the sites, with check permutations $\pi_X,\pi_Z$, such that
--   $$H_\sigma(\pi_\sigma a,\pi_s i)=H_\sigma(a,i)\quad\text{and}\quad a^{(\sigma)}(s\circ\pi_\sigma)=a^{(\sigma)}(s)\circ\pi_s,$$
--   there is a permutation of the registers, moving each register with its site and keeping its sector, whose combined action on $\mathcal H^{\mathrm{ext}}$ commutes with $\mathcal L(t)$.
--
--   These are the "geometrically local", "periodic" and "translationally invariant" clauses of Theorem 4.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.23, p. 20 (PDF p. 22); Theorem 4, p. 31 (PDF p. 33); Definition 7.7, eq. (193), p. 56 (PDF p. 58)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Supplement_RegSyndromeLindbladian
import Definitions.Def_AutoQMem_Lindblad_Supplement_IsRLocalChannel
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

variable {n mX mZ : ℕ}

/-- The registers located at the sites of `S`. -/
noncomputable def regsAt (R : Registers n) (S : Finset (Fin n)) : Finset R.Reg :=
  Finset.univ.filter fun j => R.loc j ∈ S

/-- **Support of an operator on `H^ext`**: `O` is supported on the data qubits `S` and the registers
`T` if `O = O' ⊗ I` for an operator `O'` on those qubits (Drechsler, Oreg, Aharonov, *Autonomous
Quantum Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03),
Definition 2.23, p. 20, PDF 22: "supported in N_R(i)"). -/
def IsSupportedOnExt (R : Registers n) (O : R.Op) (S : Finset (Fin n)) (T : Finset R.Reg) : Prop :=
  ∃ O' : Matrix (({i // i ∈ S} → ZMod 2) × ({j // j ∈ T} → ZMod 2))
      (({i // i ∈ S} → ZMod 2) × ({j // j ∈ T} → ZMod 2)) ℂ,
    O = Matrix.reindex (((splitAt S).prodCongr (splitAt T)).trans
          (Equiv.prodProdProdComm _ _ _ _)).symm
        (((splitAt S).prodCongr (splitAt T)).trans (Equiv.prodProdProdComm _ _ _ _)).symm
        (Matrix.kronecker O' 1)

/-- **R-local register-extended Lindbladian.** Drechsler, Oreg, Aharonov, *Autonomous Quantum
Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.23,
p. 20 (PDF 22): "A syndrome-based Lindbladian is R-local if it admits a representation as in
Equation (31) in which, for all t, every jump operator P_i f_{P,i,α}(t) is supported in N_R(i), and
H(t) = Σ_i H_i(t) with each H_i(t) ∈ A Hermitian and supported in N_R(i). … For Lindbladians with
auxiliary registers (Appendix D), the registers attached to a site i are counted as located at i."

**Formalization Note.** `N_R(i)` is taken in the interaction graph of the CSS code (`cssGraph`);
a register counts as located at its site `R.loc j`, so "supported in `N_R(i)`" means supported on
the data qubits of `N_R(i)` and the registers located there. `A` becomes `A^ext` (Definition 7.1 (i)).
The conditions are imposed for `t ≥ 0`, the domain on which the Lindbladian is defined. -/
def IsRLocalExt {C : CSSCode n mX mZ} {R : Registers n} (L : RegSyndromeLindbladian C R)
    (Rad : ℕ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ α, IsSupportedOnExt R (L.jump t α) (nbhd (cssGraph C) Rad {L.site α})
      (regsAt R (nbhd (cssGraph C) Rad {L.site α}))) ∧
  ∃ Hloc : ℝ → Fin n → R.Op, ∀ t : ℝ, 0 ≤ t → L.ham t = ∑ i, Hloc t i ∧
    ∀ i, Hloc t i ∈ R.algExt C ∧ (Hloc t i).IsHermitian ∧
      IsSupportedOnExt R (Hloc t i) (nbhd (cssGraph C) Rad {i})
        (regsAt R (nbhd (cssGraph C) Rad {i}))

/-- **Periodic with period Δ** (Theorem 4, p. 31: "a … periodic Lindbladian L_PCA(t) with period Δ";
Definition 7.7, eq. (193)): the Hamiltonian and every syndrome function of the representation
satisfy `X(t + Δ) = X(t)` for `t ≥ 0`. -/
def RegSyndromeLindbladian.IsPeriodic {C : CSSCode n mX mZ} {R : Registers n}
    (L : RegSyndromeLindbladian C R) (Δ : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → L.ham (t + Δ) = L.ham t ∧ ∀ α, L.f (t + Δ) α = L.f t α

/-- **Conjugation of an operator on `H^ext` by a permutation of the data qubits and of the registers**:
`(x, c) ↦ (x ∘ π_s, c ∘ π_R)` on basis labels. -/
def extPermConj (R : Registers n) (πs : Equiv.Perm (Fin n)) (πR : Equiv.Perm R.Reg) (O : R.Op) :
    R.Op :=
  Matrix.of fun xc yd => O (xc.1 ∘ πs, xc.2 ∘ πR) (yd.1 ∘ πs, yd.2 ∘ πR)

/-- **Translation invariance, read as equivariance** (Theorem 4, p. 31: "The Lindbladian L_PCA(t) is
translationally invariant whenever the code pair and both SPCAs are").

**Formalization Note.** A symmetry of the code pair and both rules is a permutation `π_s` of the
sites with permutations `π_X`, `π_Z` of the checks such that `H_σ(π_σ a, π_s i) = H_σ(a, i)` and
`a^{(σ)}(s ∘ π_σ) = a^{(σ)}(s) ∘ π_s` on valid syndromes (so that the SPCA update commutes with
relabelling). For each such symmetry the Lindbladian commutes with the conjugation by `π_s` on the
data and a register permutation `π_R` that moves each register with its site and keeps its sector.
Lattice translations are the case of a translation-invariant code family. -/
def IsEquivariant {C : CSSCode n mX mZ} {R : Registers n} (L : RegSyndromeLindbladian C R)
    (aX : (Fin mX → ZMod 2) → (Fin n → ZMod 2)) (aZ : (Fin mZ → ZMod 2) → (Fin n → ZMod 2)) :
    Prop :=
  ∀ (πs : Equiv.Perm (Fin n)) (πX : Equiv.Perm (Fin mX)) (πZ : Equiv.Perm (Fin mZ)),
    (∀ a i, C.HX (πX a) (πs i) = C.HX a i) → (∀ b i, C.HZ (πZ b) (πs i) = C.HZ b i) →
    (∀ s ∈ Set.range C.HX.mulVec, aX (s ∘ πX) = aX s ∘ πs) →
    (∀ s ∈ Set.range C.HZ.mulVec, aZ (s ∘ πZ) = aZ s ∘ πs) →
    ∃ πR : Equiv.Perm R.Reg, (∀ j, R.loc (πR j) = πs (R.loc j) ∧ R.isX (πR j) = R.isX j) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ ρ : R.Op,
        L.gen t (extPermConj R πs πR ρ) = extPermConj R πs πR (L.gen t ρ)

end AutoQMem.Lindblad.Supplement


