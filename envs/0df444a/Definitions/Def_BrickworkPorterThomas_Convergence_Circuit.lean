-- Prove2me | Definitions.Def_BrickworkPorterThomas_Convergence_Circuit
-- name    : BrickworkPorterThomas_Convergence_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:32.125557+00:00
-- url     : https://prove2.me/theorems/0ed4fe96-7f67-483d-bbd6-b3b652107a85
-- title:
--   Brickwork Haar random circuits $\mathcal C(l)$, the output law $p_U(b)$, $k$-fold twirls and additive approximate designs
-- statement:
--   Fix an even number $n=2M\ge2$ of qubits on a ring and write $d=2^n$. Computational basis states are bitstrings $x\in\{0,1\}^n$, and an $n$-qubit operator is a complex $d\times d$ matrix indexed by bitstrings.
--
--   1. **Haar measure.** $\mu_H$ is the normalized Haar probability measure on the compact group $\mathrm{SU}(d)$, and on $\mathrm{SU}(4)$ for two-qubit gates.
--   2. **Brickwork circuits** (Definition 2.4). A depth-$l$ circuit has $l$ parallel layers. Odd layers apply independent Haar $\mathrm{SU}(4)$ gates to the pairs $(1,2),(3,4),\dots,(n-1,n)$, even layers to $(2,3),\dots,(n-2,n-1),(n,1)$. All $lM$ gates are independent, and the layers are applied in chronological order, $U=L_l\cdots L_2L_1$. The law of $U$ is $\mathcal C(l)$.
--   3. **Output law** (Definition 2.1, Theorem 1.1). For a fixed $b\in\{0,1\}^n$, $p_U(b)=|\langle b|U|0^n\rangle|^2$. $P$ is the law of the real random variable $p_U(b)$ for $U\sim\mathcal C(l)$, and $Q$ is its law for $U\sim\mu_H$.
--   4. **Designs** (Definition 2.3). The $k$-fold twirl of a law $\nu$ is
--
--   $$
--   \mathcal M^{(k)}_\nu(\rho)=\int U^{\otimes k}\rho\,U^{\dagger\otimes k}\,d\nu(U),
--   $$
--
--   and $\nu$ is an (additive) $\varepsilon$-approximate $k$-design when $\|\mathcal M^{(k)}_\nu-\mathcal M^{(k)}_{\mu_H}\|_\diamond\le\varepsilon$. The diamond norm is the stabilized trace-norm operator norm, with no factor $1/2$ and no normalization by $d^k$. The paper's accuracy is $\varepsilon=d^{-k}$.
--   5. **Final gate and marginal masses** (Eqs. (102), (103), (114), (118)). For a circuit of depth $l+1$, a gate $G_*$ of the final layer with output pair $S_*$ is removed, so that $U=G_*C$. For a set $S$ of qubits and a string $x$, $R_S=\sum_{z\in\{0,1\}^S}|\langle z,x_{\bar S}|C|0^n\rangle|^2$, and $R=R_{S_*}$. The nested interval $S_i$ starts with $S_*$ and adds the two preceding ring wires at each step, ending with the entire ring.
--   6. **Two-gate probability** (Eq. (163)). On three qubits $q_1,q_2,q_3$, with $G$ acting first on $(q_2,q_3)$ and $H$ then on $(q_1,q_2)$, $P_\rho=\mathrm{Tr}[(|x_1x_2\rangle\langle x_1x_2|\otimes I_3)HG\rho G^\dagger H^\dagger]$.
--
--   These are the objects the paper's theorems are stated in: the brickwork ensemble, its output-probability law compared with the exact Haar law, and the design property that supplies moment matching.
--
--   **Formalization Note** Qubits and layers are 0-based. The pairs come from the reused `brickPair` (layer $j$ in Lean is the paper's layer $j+1$). The circuit is a measurable function of the gate configuration $(\mathrm{SU}(4))^{l\times M}$ with the product Haar law, and $\mathcal C(l)$ is its push-forward to the matrix space, which carries its Borel $\sigma$-algebra (supported on $\mathrm{SU}(d)$). The twirl is written entrywise, $(U^{\otimes k}\rho U^{\dagger\otimes k})_{xy}=\sum_{a,b}(U^{\otimes k})_{xa}\rho_{ab}\overline{(U^{\otimes k})_{yb}}$. Its entries are integrals of bounded continuous functions against probability laws supported on unitaries, so no integral takes a junk value. The design error is the reused diamond norm, computed after relabelling the $k$-fold basis by $\mathrm{Fin}(d^k)$. $C$ is the circuit with $G_*$ replaced by the identity. The entries of $x$ on $S$ are ignored in $R_S$.
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §2, pp. 4–5, Definitions 2.1, 2.3, 2.4 and Theorem 1.1 Eq. (1); §5, p. 15, Eqs. (102)–(103); §6, pp. 16–19, Eqs. (114), (117)–(118), (129); Appendix A, p. 23, Eq. (163); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_brickPair
import Definitions.Def_QAlgorithms_Defs_ChannelDiamondNorm

/-!
# Brickwork Haar random circuits, their output law, and approximate designs

Aniruddha Sen, Nick Hunter-Jones, *Local random quantum circuits converge to the Porter-Thomas
distribution in polynomial depth*, STOC 2027 submission #118 (October 2026), §2, pp. 4–5
(Definitions 2.1–2.4), §5, p. 15 (Eq. (103)), §6, pp. 16–20 (Eqs. (114), (117), (118), (129)),
Appendix A, p. 23 (Eq. (163)).

Qubits are indexed `0, …, n-1` (the paper's qubit `i` is index `i-1`); a computational basis
state of `N` qubits is a bitstring `Bits N = Fin N → Fin 2`, and an `N`-qubit operator is a
complex matrix indexed by bitstrings. The number of qubits of a brickwork circuit is `n = 2 * M`
with `M ≥ 1`, so every even `n ≥ 2` occurs, and `d = 2 ^ n`.
-/

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ComplexConjugate Matrix.Norms.Elementwise

namespace BrickworkPorterThomas.Convergence

/-- Computational-basis labels of `N` qubits: bitstrings `x ∈ {0,1}^N`. -/
abbrev Bits (N : ℕ) := Fin N → Fin 2

/-- The all-zeros bitstring `0^N`, the input state `|0^N⟩`. -/
def zeroBits (N : ℕ) : Bits N := fun _ => 0

/-- `N`-qubit operators: complex `2^N × 2^N` matrices indexed by bitstrings. -/
abbrev QMat (N : ℕ) := Matrix (Bits N) (Bits N) ℂ

/-- The special unitary group `SU(ι)` of complex matrices indexed by `ι`, with the subspace
topology of the matrix space. -/
abbrev SU (ι : Type) [Fintype ι] [DecidableEq ι] := Matrix.specialUnitaryGroup ι ℂ

section Haar

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Matrix multiplication is continuous on `SU(ι)`, and the inverse is the conjugate transpose,
which is continuous: `SU(ι)` is a topological group. -/
instance instTopGroupSU : IsTopologicalGroup (SU ι) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.matrix_conjTranspose

/-- `SU(ι)` is compact: it is closed (unitarity and `det = 1` are closed conditions) and
bounded (all entries of a unitary have modulus at most one). -/
instance instCompactSU : CompactSpace (SU ι) := by
  have hc : IsClosed (SU ι : Set (Matrix ι ι ℂ)) := by
    have h1 : IsClosed (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := isClosed_unitary
    have h2 : IsClosed {A : Matrix ι ι ℂ | A.det = 1} :=
      isClosed_eq (continuous_id.matrix_det) continuous_const
    have : (SU ι : Set (Matrix ι ι ℂ)) =
        (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) ∩ {A | A.det = 1} := by
      ext A
      simp [Matrix.mem_specialUnitaryGroup_iff]
    rw [this]
    exact h1.inter h2
  have hb : Bornology.IsBounded (SU ι : Set (Matrix ι ι ℂ)) := by
    refine (Metric.isBounded_closedBall (x := (0 : Matrix ι ι ℂ)) (r := 1)).subset ?_
    intro U hU
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact entrywise_sup_norm_bound_of_unitary (Matrix.mem_specialUnitaryGroup_iff.mp hU).1
  exact isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded hc hb)

/-- Borel σ-algebra on `SU(ι)`. -/
instance instMeasSU : MeasurableSpace (SU ι) := borel _

instance instBorelSU : BorelSpace (SU ι) := ⟨rfl⟩

/-- §2, p. 4: the normalized Haar measure `μ_H` on `SU(ι)`, the left-invariant regular measure
normalized so that the whole (compact) group has measure `1`. -/
def haarSU (ι : Type) [Fintype ι] [DecidableEq ι] : Measure (SU ι) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts (SU ι))

example : haarSU ι Set.univ = 1 := Measure.haarMeasure_self

end Haar

/-- Borel σ-algebra on the space of `N`-qubit matrices (product topology of the entries); the
laws `ν` on `SU(d)` of Definition 2.3 are realized as laws on matrices supported on `SU(d)`. -/
scoped instance instMeasQMat (N : ℕ) : MeasurableSpace (QMat N) := borel _

scoped instance instBorelQMat (N : ℕ) : BorelSpace (QMat N) := ⟨rfl⟩

/-- A two-qubit gate `G ∈ SU(4)`, acting on the two-qubit basis `Bits 2`. -/
abbrev SU4 := SU (Bits 2)

open Classical in
/-- The two-qubit operator `G` applied to the ordered qubit pair `e 0, e 1` of an `N`-qubit
register, tensored with the identity on every other qubit:
`⟨x| G_{e} |y⟩ = ⟨x_{e0} x_{e1}| G |y_{e0} y_{e1}⟩` if `x` and `y` agree off the pair, else `0`. -/
def liftGate {N : ℕ} (e : Fin 2 ↪ Fin N) (G : QMat 2) : QMat N :=
  fun x y => if (∀ q, q ∉ Set.range e → x q = y q) then G (x ∘ e) (y ∘ e) else 0

/-- Definition 2.4, p. 5: one parallel layer of a brickwork circuit on `n = 2M` qubits. Layer `j`
(0-based; the paper's layer `j+1`) applies gate `g p` to the pair `brickPair M j p`: for the paper's
odd layers (`j` even) the pairs `(1,2),(3,4),…,(n-1,n)`, for its even layers (`j` odd) the pairs
`(2,3),…,(n-2,n-1),(n,1)` (periodic boundary). The gates of a layer act on disjoint pairs and
commute; the product is taken in the order `p = 0, 1, …, M-1`. -/
def layerMat (M j : ℕ) (g : Fin M → SU4) : QMat (2 * M) :=
  ((List.finRange M).map fun p => liftGate (ShallowShadows.ShadowNorm.brickPair M j p) (g p).val).prod

/-- A gate configuration of a depth-`l` brickwork circuit on `2M` qubits: one `SU(4)` gate for
each of the `l` layers and each of the `M` pairs of that layer. -/
abbrev Gates (M l : ℕ) := Fin l → Fin M → SU4

/-- Definition 2.4, p. 5: the circuit unitary `U = L_{l-1} ⋯ L_1 L_0`, layers applied
chronologically (layer `0` first). Depth counts individual parallel layers. -/
def circuitMat (M l : ℕ) (g : Gates M l) : QMat (2 * M) :=
  (List.finRange l).foldl (fun U (j : Fin l) => layerMat M j.val (g j) * U) 1

/-- Definition 2.4, p. 5: the gate law of `C(l)`: all `l · M` gates independent, each distributed
according to the normalized Haar measure on `SU(4)`. -/
def gateLaw (M l : ℕ) : Measure (Gates M l) :=
  Measure.pi fun _ : Fin l => Measure.pi fun _ : Fin M => haarSU (Bits 2)

/-- The brickwork ensemble `C(l)` as a law on `2M`-qubit matrices (supported on `SU(2^{2M})`). -/
def circuitLaw (M l : ℕ) : Measure (QMat (2 * M)) :=
  (gateLaw M l).map (circuitMat M l)

/-- The Haar law `μ_H` on `SU(2^N)`, as a law on `N`-qubit matrices. -/
def haarLaw (N : ℕ) : Measure (QMat N) :=
  (haarSU (Bits N)).map Subtype.val

/-- Definition 2.1, p. 5: the output probability `p_U(b) = |⟨b|U|0^N⟩|²`. -/
def outProb {N : ℕ} (b : Bits N) (U : QMat N) : ℝ :=
  ‖U b (zeroBits N)‖ ^ 2

/-- Theorem 1.1, Eq. (1), p. 2: the law `P` of the real random variable `p_U(b)`, `U ∼ C(l)`. -/
def outputLaw (M l : ℕ) (b : Bits (2 * M)) : Measure ℝ :=
  (gateLaw M l).map fun g => outProb b (circuitMat M l g)

/-- Theorem 1.1, p. 2: the law `Q` of `p_U(b)` for `U` Haar random on `SU(2^N)`. -/
def haarOutputLaw (N : ℕ) (b : Bits N) : Measure ℝ :=
  (haarSU (Bits N)).map fun U => outProb b U.val

/-- The `k`-fold tensor power `U^{⊗k}`, indexed by `k`-tuples of bitstrings. -/
def tensorPow {N : ℕ} (k : ℕ) (U : QMat N) : Matrix (Fin k → Bits N) (Fin k → Bits N) ℂ :=
  fun x y => ∏ j, U (x j) (y j)

/-- The coefficients `∫ (U^{⊗k})_{x a} conj((U^{⊗k})_{y b}) dν(U)` of the `k`-fold twirl. -/
def twirlCoeff {N : ℕ} (ν : Measure (QMat N)) (k : ℕ) (x y a b : Fin k → Bits N) : ℂ :=
  ∫ U, tensorPow k U x a * conj (tensorPow k U y b) ∂ν

/-- Definition 2.3, p. 5: the `k`-fold twirl `M_ν^{(k)}(ρ) = ∫ U^{⊗k} ρ U^{†⊗k} dν(U)`, written
entrywise (`(U^{⊗k} ρ U^{†⊗k})_{xy} = Σ_{a,b} (U^{⊗k})_{xa} ρ_{ab} conj((U^{⊗k})_{yb})`), a
complex-linear map on operators of the `k`-fold system. -/
def twirl {N : ℕ} (ν : Measure (QMat N)) (k : ℕ) :
    Matrix (Fin k → Bits N) (Fin k → Bits N) ℂ →ₗ[ℂ]
      Matrix (Fin k → Bits N) (Fin k → Bits N) ℂ where
  toFun ρ := Matrix.of fun x y => ∑ a, ∑ b, twirlCoeff ν k x y a b * ρ a b
  map_add' ρ σ := by
    ext x y
    simp only [Matrix.of_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c ρ := by
    ext x y
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-- The `k`-fold system relabelled by `Fin (2^N)^k`, the index type of the reused diamond norm. -/
def kfoldEquiv (N k : ℕ) : (Fin k → Bits N) ≃ Fin (Fintype.card (Fin k → Bits N)) :=
  Fintype.equivFin _

/-- Definition 2.3, p. 5: the additive design error `‖M_ν^{(k)} − M_{μ_H}^{(k)}‖_⋄`, the full
stabilized trace-norm diamond norm of the difference of the twirls (no factor `1/2`, no
normalization by `d^k`), computed after relabelling the `k`-fold basis by `Fin (2^N)^k`. -/
def designError {N : ℕ} (ν : Measure (QMat N)) (k : ℕ) : ℝ :=
  QAlgorithms.IntrinsicLearning.diamondNorm (Fintype.card (Fin k → Bits N)) Fintype.card_pos
    ((Matrix.reindexLinearEquiv ℂ ℂ (kfoldEquiv N k) (kfoldEquiv N k)).toLinearMap ∘ₗ
      (twirl ν k - twirl (haarLaw N) k) ∘ₗ
      (Matrix.reindexLinearEquiv ℂ ℂ (kfoldEquiv N k).symm (kfoldEquiv N k).symm).toLinearMap)

/-- Definition 2.3, p. 5: `ν` is an (additive) `ε`-approximate unitary `k`-design. -/
def IsApproxDesign {N : ℕ} (ν : Measure (QMat N)) (k : ℕ) (ε : ℝ) : Prop :=
  designError ν k ≤ ε

/-- The design accuracy `d^{-k}` with `d = 2^{2M}` used throughout the paper. -/
def designTol (M k : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * M))⁻¹ ^ k

/-! ### The final gate and marginal masses (§5, p. 15; §6, pp. 16–20) -/

/-- The gate configuration of a depth-`(l+1)` circuit with the final-layer gate `p` (the gate
`G_*` of Lemma 5.2 / Theorem 6.1) replaced by the identity. -/
def removeFinal {M l : ℕ} (g : Gates M (l + 1)) (p : Fin M) : Gates M (l + 1) :=
  fun j q => if j = Fin.last l ∧ q = p then 1 else g j q

/-- Eq. (102): the remaining circuit `C`, so that `U = G_* C`. -/
def restCircuit {M l : ℕ} (g : Gates M (l + 1)) (p : Fin M) : QMat (2 * M) :=
  circuitMat M (l + 1) (removeFinal g p)

/-- The output pair `S_*` of the final-layer gate `p` (final layer index `l`, 0-based). -/
def finalPair (M l : ℕ) (p : Fin M) : Finset (Fin (2 * M)) :=
  Finset.univ.map (ShallowShadows.ShadowNorm.brickPair M l p)

open Classical in
/-- Section 6, pp. 17–19: the actual nested intervals `S_i`, starting at `S_*` and
adding the two preceding ring wires at every step. Index `i : Fin M` gives `2(i+1)`
free wires; `i = M-1` gives the whole ring. The formula uses residues modulo `2M`.
The subtraction is not truncated on this domain, since `i < M`. -/
def expandedInterval (M l : ℕ) (p i : Fin M) : Finset (Fin (2 * M)) :=
  Finset.univ.filter fun q => ∃ j < 2 * (i.val + 1),
    q.val = ((ShallowShadows.ShadowNorm.brickPair M l p 0).val +
      2 * M - 2 * i.val + j) % (2 * M)

/-- The bitstring equal to `z` on `S` and to `x` off `S` (written `|z, x_{\bar S}⟩`). -/
def glue {N : ℕ} (S : Finset (Fin N)) (z : S → Fin 2) (x : Bits N) : Bits N :=
  fun q => if h : q ∈ S then z ⟨q, h⟩ else x q

/-- Eq. (118), p. 18 (and Eq. (129)): the probability mass
`R_S = Σ_{z ∈ {0,1}^S} |⟨z, x_{\bar S}| C |0^n⟩|²` of the remaining circuit `C` on outputs agreeing
with `x` off the qubit set `S`; only the entries of `x` outside `S` enter. -/
def marginalMass {M l : ℕ} (p : Fin M) (S : Finset (Fin (2 * M))) (x : Bits (2 * M))
    (g : Gates M (l + 1)) : ℝ :=
  ∑ z : S → Fin 2, ‖restCircuit g p (glue S z x) (zeroBits (2 * M))‖ ^ 2

/-- Eqs. (103) and (114): `R = Σ_{z ∈ {0,1}^{S_*}} |⟨z, x|C|0^n⟩|²`, the mass entering the
final gate `G_*`, for a fixed string `x` on the complement of `S_*` (entries of `x` on `S_*` are
ignored). -/
def finalGateMass {M l : ℕ} (p : Fin M) (x : Bits (2 * M)) (g : Gates M (l + 1)) : ℝ :=
  marginalMass p (finalPair M l p) x g

/-! ### The two-gate configuration of Lemma A.2 (p. 23) -/

/-- The pair `(q₂, q₃)` (indices `1, 2`) of three consecutive qubits `q₁, q₂, q₃`. -/
def pair23 : Fin 2 ↪ Fin 3 :=
  ⟨![1, 2], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

/-- The pair `(q₁, q₂)` (indices `0, 1`). -/
def pair12 : Fin 2 ↪ Fin 3 :=
  ⟨![0, 1], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

/-- The projector `|x₁x₂⟩⟨x₁x₂| ⊗ I₃` on three qubits. -/
def projX12 (x₁ x₂ : Fin 2) : QMat 3 :=
  Matrix.diagonal fun y => if y 0 = x₁ ∧ y 1 = x₂ then 1 else 0

/-- Eq. (163), p. 23: `P_ρ = Tr[(|x₁x₂⟩⟨x₁x₂| ⊗ I₃) H G ρ G† H†]`, where `G` acts first on
`(q₂, q₃)` and `H` then on `(q₁, q₂)`. -/
def twoGateProb (x₁ x₂ : Fin 2) (ρ : QMat 3) (G H : SU4) : ℝ :=
  let A : QMat 3 := liftGate pair12 H.val * liftGate pair23 G.val
  (Matrix.trace (projX12 x₁ x₂ * (A * ρ * A.conjTranspose))).re

end BrickworkPorterThomas.Convergence


