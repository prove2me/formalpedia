-- Prove2me | Definitions.Def_KochHF_Hamiltonian
-- name    : KochHF_Hamiltonian
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:23:05.888863+00:00
-- url     : https://prove2.me/theorems/bf0535fc-6cf1-4761-a725-b7e716b17d06
-- title:
--   Hartree-Fock Hamiltonian, Fock matrix and orbital energies
-- statement:
--   Let $T$ be a complex $K\times K$ matrix (one-body matrix elements) and $U_{nn',mm'}$ a complex 4-index array (two-body matrix elements). Following Sec. 3.2 the **Hamiltonian with one- and two-body terms** is
--   $$\hat H=\sum_{n,m}c^\dagger_n\,T_{nm}\,c_m+\sum_{n>n',\,m>m'}c^\dagger_n c^\dagger_{n'}\bigl(U_{nn',mm'}-U_{nn',m'm}\bigr)c_{m'}c_m .$$
--
--   For a set $S$ of occupied reference orbitals (the determinant $|S\rangle$):
--
--   1. $\Delta_{mm'}=U_{mm',mm'}-U_{mm',m'm}$ (Eq. (65));
--   2. the **Fock matrix** (Eq. (64)) $F_{nm}=T_{nm}+\sum_{m'\in S}\bigl(U_{nm',mm'}-U_{nm',m'm}\bigr)$;
--   3. the **Hartree-Fock orbital energy** (Eq. (65)) $\varepsilon_m=F_{mm}=T_{mm}+\sum_{m'\in S}\Delta_{mm'}$;
--   4. the **determinant energy** $E(S)=\langle S|\hat H|S\rangle$.
--
--   These definitions are used in the milestones on the Fock matrix, the Hartree-Fock energy, Koopmans' theorem and electron-hole excitation energies.
--
--   **Formalization Note** The occupied orbitals are an arbitrary subset $S$ of the reference orbitals rather than the first $N$ of them; $\varepsilon_m$ is defined as the diagonal entry $F_{mm}$, which is the source's Eq. (65) and coincides with the Fock eigenvalue when $F$ is diagonal (self-consistency).
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 3.2, pp. 2.17–2.18: Hamiltonian preceding Eq. (64), Eqs. (64), (65).

import Mathlib
import Definitions.Def_KochHF_FockSpace

/-!
# The Hartree-Fock Hamiltonian, Fock matrix and orbital energies

E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, Sec. 3.2 (Hamiltonian before Eq. (64),
Eqs. (64), (65)).
-/

noncomputable section

namespace KochHF

/-- `Ĥ = Σ_{n,m} c†_n T_{nm} c_m + Σ_{n>n', m>m'} c†_n c†_{n'} (U_{nn',mm'} - U_{nn',m'm}) c_{m'} c_m`
(Sec. 3.2). -/
def hamiltonian {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ) (U : Fin K → Fin K → Fin K → Fin K → ℂ) :
    FockOp K :=
  (∑ n, ∑ m, T n m • (cdag n * cann m)) +
    ∑ n, ∑ n', ∑ m, ∑ m',
      if n' < n ∧ m' < m then
        (U n n' m m' - U n n' m' m) • (cdag n * cdag n' * cann m' * cann m)
      else 0

/-- `Δ_{mm'} = U_{mm',mm'} - U_{mm',m'm}` (Eq. (65)). -/
def hfDelta {K : ℕ} (U : Fin K → Fin K → Fin K → Fin K → ℂ) (m m' : Fin K) : ℂ :=
  U m m' m m' - U m m' m' m

/-- Fock matrix of the determinant with occupied reference orbitals `S` (Eq. (64)):
`F_{nm} = T_{nm} + Σ_{m' ∈ S} (U_{nm',mm'} - U_{nm',m'm})`. -/
def fockMatrix {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ) (U : Fin K → Fin K → Fin K → Fin K → ℂ)
    (S : Finset (Fin K)) (n m : Fin K) : ℂ :=
  T n m + ∑ m' ∈ S, (U n m' m m' - U n m' m' m)

/-- Hartree-Fock orbital energy `ε_m = F_{mm} = T_{mm} + Σ_{m' ∈ S} Δ_{mm'}` (Eq. (65)). -/
def hfOrbitalEnergy {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ)
    (U : Fin K → Fin K → Fin K → Fin K → ℂ) (S : Finset (Fin K)) (m : Fin K) : ℂ :=
  fockMatrix T U S m m

/-- Energy expectation value `⟨S|Ĥ|S⟩` of the Slater determinant `|S⟩ = Π_{m ∈ S} c†_m |0⟩`
of reference orbitals. -/
def detEnergy {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ) (U : Fin K → Fin K → Fin K → Fin K → ℂ)
    (S : Finset (Fin K)) : ℂ :=
  matEl (basisState S) (hamiltonian T U) (basisState S)

end KochHF

end


