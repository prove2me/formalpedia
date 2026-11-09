-- Prove2me | Definitions.Def_LindbladTolerant_Testing_lindblad_model
-- name    : LindbladTolerant_Testing_lindblad_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:52:36.910333+00:00
-- url     : https://prove2.me/theorems/1e690b5d-70a3-4399-8302-e9d938d08cf1
-- title:
--   Canonical Lindblad data and single-support jump locality
-- statement:
--   The computational basis on $n$ qubits is indexed by bit strings, with $d=2^n$. A Lindblad representation consists of a Hermitian Hamiltonian $H$ and a finite family of traceless matrices $L_a$; the family may be empty. Set
--   $$
--   A=\sum_aL_a^\dagger L_a,\quad
--   \mathcal D(X)=\sum_aL_aXL_a^\dagger-\tfrac12(AX+XA),\quad
--   \mathcal L(X)=-i(HX-XH)+\mathcal D(X).
--   $$
--   Write $\Phi=d^{-1/2}\sum_j|j,j\rangle$ and $\Pi=I-|\Phi\rangle\langle\Phi|$. Independently of any chosen representation, define
--   $$
--   C(\mathcal L)=\Pi J(\mathcal L)\Pi,\quad A(\mathcal L)=d\bigl(\operatorname{Tr}_S C(\mathcal L)\bigr)^T,\quad
--   \Gamma(\mathcal L)=\operatorname{Tr}C(\mathcal L).
--   $$
--   The canonical dissipator is reconstructed from the inverse Choi map of $C$ and this $A$. Agreement with representation data is the content of Lemma 2.3. For $\Gamma>0$, define $\sigma=C/\Gamma$, $\sigma_R=\operatorname{Tr}_S\sigma$, and
--   $$h(\sigma)=\operatorname{Tr}(\sigma^2)+\tfrac12\bigl(d\operatorname{Tr}(\sigma_R^2)-1\bigr).$$
--   No jump state is assigned when $\Gamma=0$.
--
--   Each Pauli string is a tensor product of $I,X,Y,Z$. A jump is $k$-local when there is one support set of at most $k$ sites containing the support of every nonzero Pauli coefficient of that jump. Locality of a generator means existence of a traceless local representation. The source class also requires $\|\mathcal L\|_\diamond\le\Lambda$, without a separate Hamiltonian bound, degree bound, or bound on the number or overlap of supports.
--
--   These definitions are shared by the algebraic identities, the estimator, and the time bounds. They do not assume any of those results.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, §§2.1,2.3–2.4, pp.9–16, PDF pp.9–16, Eqs.(18)–(28), Definition 2.9

import Definitions.Def_LindbladTolerant_Testing_matrix_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators ComplexConjugate Matrix

namespace LindbladTolerant.Testing

abbrev Qubits (n : ℕ) := Fin n → Bool
abbrev Pauli (n : ℕ) := Fin n → Fin 4

def onePauli (p : Fin 4) : Op Bool := fun x y =>
  if p = 0 then if x = y then 1 else 0
  else if p = 1 then if x ≠ y then 1 else 0
  else if p = 2 then if x = false ∧ y = true then -Complex.I
    else if x = true ∧ y = false then Complex.I else 0
  else if x = y then if x = false then 1 else -1 else 0

def pauliMatrix {n : ℕ} (p : Pauli n) : Op (Qubits n) :=
  fun x y => ∏ i, onePauli (p i) (x i) (y i)

def support {n : ℕ} (p : Pauli n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ≠ 0)
def weight {n : ℕ} (p : Pauli n) : ℕ := (support p).card

def pauliCoefficient {n : ℕ} (l : Op (Qubits n)) (p : Pauli n) : ℂ :=
  (pauliMatrix p * l).trace / (2^n : ℂ)

def IsLocalJump {n : ℕ} (k : ℕ) (l : Op (Qubits n)) : Prop :=
  ∃ s : Finset (Fin n), s.card ≤ k ∧
    ∀ p : Pauli n, ¬ support p ⊆ s → pauliCoefficient l p = 0

/-- A representation is finite, traceless, and may have no jumps. It imposes no
locality, Hamiltonian strength, degree or overlap assumption. -/
structure LindbladRepresentation (n : ℕ) where
  hamiltonian : Op (Qubits n)
  hermitian : hamiltonian.IsHermitian
  count : ℕ
  jump : Fin count → Op (Qubits n)
  traceless : ∀ a, (jump a).trace = 0

variable {n : ℕ}

def hamiltonianGenerator (h : Op (Qubits n)) : Super (Qubits n) (Qubits n) :=
  (-Complex.I) • (leftRight h 1 - leftRight 1 h)

def representationA (r : LindbladRepresentation n) : Op (Qubits n) :=
  ∑ a, (r.jump a).conjTranspose * r.jump a

def representationC (r : LindbladRepresentation n) : Op (Qubits n × Qubits n) :=
  ∑ a, outer (ket (r.jump a)) (ket (r.jump a))

def representationD (r : LindbladRepresentation n) : Super (Qubits n) (Qubits n) :=
  (∑ a, conjugation (r.jump a)) -
    (1/2 : ℂ) • (leftRight (representationA r) 1 + leftRight 1 (representationA r))

def generator (r : LindbladRepresentation n) : Super (Qubits n) (Qubits n) :=
  hamiltonianGenerator r.hamiltonian + representationD r

def IsLindblad (g : Super (Qubits n) (Qubits n)) : Prop :=
  ∃ r : LindbladRepresentation n, generator r = g

/-- Canonical data are computed from the projected Choi block. Lemma 2.3 must
prove agreement with representation data; no such identity is an axiom. -/
def canonicalC (g : Super (Qubits n) (Qubits n)) : Op (Qubits n × Qubits n) :=
  orthogonalProjector * choi g * orthogonalProjector

def canonicalA (g : Super (Qubits n) (Qubits n)) : Op (Qubits n) :=
  (2^n : ℂ) • (traceSystem (canonicalC g)).transpose

def canonicalD (g : Super (Qubits n) (Qubits n)) : Super (Qubits n) (Qubits n) :=
  inverseChoi (canonicalC g) -
    (1/2 : ℂ) • (leftRight (canonicalA g) 1 + leftRight 1 (canonicalA g))

def rate (g : Super (Qubits n) (Qubits n)) : ℝ := (canonicalC g).trace.re

/-- No jump state is defined at zero rate: every use carries the positive-rate domain. -/
def jumpState (g : Super (Qubits n) (Qubits n)) (_positive : 0 < rate g) :
    Op (Qubits n × Qubits n) := ((rate g : ℂ)⁻¹) • canonicalC g

def functional (sigma : Op (Qubits n × Qubits n)) : ℝ :=
  (sigma * sigma).trace.re + ((2^n : ℝ) *
    (traceSystem sigma * traceSystem sigma).trace.re - 1) / 2

/-- Existential locality of a representation, rather than locality of every representation. -/
def LocalGenerator (k : ℕ) (g : Super (Qubits n) (Qubits n)) : Prop :=
  ∃ r : LindbladRepresentation n, generator r = g ∧ ∀ a, IsLocalJump k (r.jump a)

def SourceClass (k : ℕ) (bound : ℝ) (g : Super (Qubits n) (Qubits n)) : Prop :=
  LocalGenerator k g ∧ diamond g ≤ bound

end LindbladTolerant.Testing


