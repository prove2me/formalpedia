-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P78
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P78
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:54:59.63493+00:00
-- url     : https://prove2.me/theorems/f5ac0d3a-024a-4827-89a2-fc5ae49a4ef5
-- title:
--   Definitions for Generic Quantum Fourier Transforms
-- statement:
--   The objects the formalized statements of *Generic Quantum Fourier Transforms* (arXiv:quant-ph/0304064) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `packDigits`: Fixed-length digit packing; no data-dependent choice of binary encoding. Source: PDF p.6, product-coset and path registers.
--   - `encodedWave`: Linear embedding of amplitudes into explicitly named computational codes. Unused wires are zero because every code is a padded binary integer. Source: PDF pp.1–3,6.
--   - `normalizedAmplitudes`: The source's normalization of the entire input, not of each coset piece. Source: PDF pp.1–2 and equation (4), p.6.
--   - `realizesEncodedTransform`: A fixed clean-input/clean-output implementation on every normalized input; the circuit is chosen outside the quantifier over f. Invalid binary strings are unconstrained. Source: Definition 1, p.3, and equations (4)–(5), p.6.
--   - `SymmetricCosetDigits`: The transversal digit at level i+1 specifies the position to which the new letter is moved. This is the point-stabilizer tower of PDF pp.4–5,8.
--   - `nextIndex`: Next letter, with a total harmless value at the unused last position.
--   - `BoundedYoungPath`: A standard tableau is an injective sequence of boxes whose every prefix is a lower ideal. Coordinates are bounded by n; no tableau with n boxes is lost. Source: Bratteli paths, p.4, and Young orthogonal basis, pp.5,8. The concrete convention follows accepted Support21.P07/ Renew46.P26; these paper modules are not imported.
--   - `youngPathEndpoint`: The actual endpoint Young diagram, computed from the path.
--   - `YoungEndpointPaths`: Paths with a fixed endpoint. Unoccupied shapes contribute no rows.
--   - `SymmetricFrequency`: Fourier labels are pairs of paths with the same endpoint, including all diagonal pairs; the endpoint itself is recorded once. Source: PDF pp.4–6.
--   - `boundedBoxContent`: Column minus row, fixing the sign of Young's orthogonal coefficients.
--   - `youngAdjacent`: The Young orthogonal matrix of the adjacent transposition (i,i+1), with row U and column T. Same-row/column cases precede division; the mixed case has positive square root and r=content(i+1)-content(i). Source: named Young orthogonal realization, PDF pp.5,8; coefficient convention is the accepted Support21.P07.youngActionCoefficient, written out locally.
--   - `symmetricWord`: The chosen coset product, largest subgroup first: the level-i factor is s_digit ... s_(i-1). Source: input encoding p.6 and point stabilizers p.8.
--   - `symmetricElement`: The actual permutation specified by the source transversal digits.
--   - `symmetricMatrix`: The representation matrix is computed from that same word, in the fixed Young orthogonal basis, before any implementation is quantified.
--   - `symmetricFourier`: Normalized plus-sign Fourier transform: no conjugation or inverse g. The representation dimension is the number of tableaux of its shape. Source: Definition 1, PDF p.3; symmetric application, pp.5,8.
--   - `symmetricInputCode`: Binary encoding of the chosen transversal digits.
--   - `tableauDigits`: Each tableau is encoded by its successive row/column coordinates. The shape is recoverable from either tableau and is not independently chosen.
--   - `symmetricOutputCode`: Fixed output encoding of the two paths. Extra wires are zero.
--   - `CliffordElement`: Coordinates (-1)^s x_n^u_n ... x_1^u_1, including the central sign. Source: finite Clifford monomial groups, PDF p.8.
--   - `cliffordCross`: The crossing sign for descending monomials: a left x_i crosses a right x_j exactly when i<j. This fixes the actual group law, including -1.
--   - `cliffordMul`: Multiplication of signed ordered monomials.
--   - `centralSignScalar`: Scalar corresponding to a central sign bit.
--   - `matrixX`: Pauli matrices used only to specify the based irreducibles explicitly.
--   - `matrixY`: The Y sign fixes the phase convention of the adapted Clifford rows.
--   - `matrixZ`: The first Clifford generator is diagonal in its adapted row basis.
--   - `CliffordSector`: Even rank has one nonlinear irrep; odd rank has two.
--   - `cliffordGenerator`: The explicit adapted irreducible generators are Y^r Z and Y^r X on successive tensor factors; at odd rank the last is either sign of Y^(tensor m). Thus restriction to the earlier even level repeats literally equal blocks, while the next odd level is selected by the last row bit. Source: p.8.
--   - `CliffordFrequency`: All 2^n linear characters, and all matrix entries of the nonlinear irrep(s). No multiplicity edge is identified with another. Source: p.8.
--   - `cliffordCoefficient`: The based matrix element at an actual signed monomial. The sign acts trivially in the linear characters and as -I in the nonlinear sectors.
--   - `cliffordDimension`: Definition 1's dimension factor for each Clifford Fourier row.
--   - `cliffordFourier`: The source's normalized plus Fourier transform of the signed monomial coordinates, whose group order is 2^(n+1). Source: PDF pp.3,8.
--   - `cliffordInputCode`: Top-down monomial tower coordinates with the central sign at the bottom.
--   - `cliffordOutputCode`: Character sectors followed by nonlinear block/row/column sectors.
--   - `QuaternionFrequency`: All four one-dimensional characters, and the row/column entries of the n-1 two-dimensional induced irreducibles. Source: cyclic subgroup, p.10.
--   - `quaternionCyclicPhase`: The plus-sign cyclic character phase, not its complex conjugate. Used only with N=2n>0 in the quaternion theorem. Source: Definition 1, p.3.
--   - `quaternionCharacterX`: Scalar of gamma in the character whose a-value is (-1)^e. Its square is (-1)^(ne), including odd n; the second bit chooses the root.
--   - `quaternionTwiddle`: The source square root C(gamma), before the separate orbit permutation.
--   - `quaternionCoefficient`: Complete fixed cyclic-subgroup-adapted matrix coefficients. For the 2D sector k=1,...,n-1, a is diag(z,z^-1) and gamma is C_k times the swap, where C_k=1 for even k and C_k=i for odd k, as on source p.10. The orbit permutation and the nonsplit square gamma^2=a^n are retained; the scalar C(gamma) is not substituted for the whole induced matrix. Source: PDF p.10; QuaternionGroup uses constructors a(j), xa(j)=gamma*a^j.
--   - `quaternionDimension`: The irreducible dimension entering the square-root normalization.
--   - `quaternionFourier`: The normalized plus QFT of the actual Mathlib QuaternionGroup. Source: Definition 1 p.3 and the general-n application p.10.
--   - `quaternionInputCode`: Source cyclic-coset encoding: a(j) has code j, gamma*a(j) code 2n+j.
--   - `quaternionOutputCode`: Fixed character/block/row/column ordering, with no arbitrary relabeling.
-- source:
--   Generic Quantum Fourier Transforms, arXiv:quant-ph/0304064v1, https://arxiv.org/abs/quant-ph/0304064v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_SpectralFilter

/-!
Generic Quantum Fourier Transforms, arXiv:quant-ph/0304064v1.
The three concrete targets below are defined independently of their circuits.
Only the literal ideal one/two-qubit gate-count claim is stated. Other planned
nodes are accounted for in HARD.md and GAPS.json, without replacement lemmas.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P78

open QAlgorithms

attribute [local instance] Classical.propDecidable

/-- Fixed-length digit packing; no data-dependent choice of binary encoding.
Source: PDF p.6, product-coset and path registers. -/
def packDigits (width : ℕ) (digits : List ℕ) : ℕ :=
  digits.foldr (fun digit rest => digit + 2 ^ width * rest) 0

/-- Linear embedding of amplitudes into explicitly named computational codes.
Unused wires are zero because every code is a padded binary integer.
Source: PDF pp.1–3,6. -/
def encodedWave {X : Type*} [Fintype X] {q : ℕ}
    (code : X → Qubits q) (f : X → ℂ) : EuclideanSpace ℂ (Qubits q) :=
  ∑ x, f x • ket (code x)

/-- The source's normalization of the entire input, not of each coset piece.
Source: PDF pp.1–2 and equation (4), p.6. -/
def normalizedAmplitudes {X : Type*} [Fintype X] (f : X → ℂ) : Prop :=
  ∑ x, Complex.normSq (f x) = 1

/-- A fixed clean-input/clean-output implementation on every normalized input;
the circuit is chosen outside the quantifier over f. Invalid binary strings
are unconstrained. Source: Definition 1, p.3, and equations (4)–(5), p.6. -/
def realizesEncodedTransform {X Y : Type*} [Fintype X] [Fintype Y] {q : ℕ}
    (c : Circuit oneTwoQubitGateSet q) (input : X → Qubits q)
    (output : Y → Qubits q) (F : (X → ℂ) → (Y → ℂ)) : Prop :=
  ∀ f, normalizedAmplitudes f →
    act c.unitary (encodedWave input f) = encodedWave output (F f)

/-- Empty digit strings have the zero code. -/
example (width : ℕ) : packDigits width [] = 0 := rfl

/-- The zero amplitude function is not a normalized state. -/
example {X : Type*} [Fintype X] : ¬ normalizedAmplitudes (fun _ : X => (0 : ℂ)) := by
  simp [normalizedAmplitudes]

/-- The transversal digit at level i+1 specifies the position to which the
new letter is moved. This is the point-stabilizer tower of PDF pp.4–5,8. -/
abbrev SymmetricCosetDigits (n : ℕ) := (i : Fin n) → Fin (i.val + 1)

/-- Next letter, with a total harmless value at the unused last position. -/
def nextIndex {n : ℕ} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else i

/-- A standard tableau is an injective sequence of boxes whose every prefix
is a lower ideal. Coordinates are bounded by n; no tableau with n boxes is
lost. Source: Bratteli paths, p.4, and Young orthogonal basis, pp.5,8.
The concrete convention follows accepted Support21.P07/ Renew46.P26;
these paper modules are not imported. -/
abbrev BoundedYoungPath (n : ℕ) :=
  {t : Fin n → Fin n × Fin n // Function.Injective t ∧
    ∀ m : ℕ, m ≤ n → IsLowerSet {b | ∃ i : Fin n, i.val < m ∧ t i = b}}

/-- The actual endpoint Young diagram, computed from the path. -/
def youngPathEndpoint {n : ℕ} (T : BoundedYoungPath n) : Finset (Fin n × Fin n) :=
  Finset.univ.image T.val

/-- Paths with a fixed endpoint. Unoccupied shapes contribute no rows. -/
abbrev YoungEndpointPaths (n : ℕ) (shape : Finset (Fin n × Fin n)) :=
  {T : BoundedYoungPath n // youngPathEndpoint T = shape}

/-- Fourier labels are pairs of paths with the same endpoint,
including all diagonal pairs; the endpoint itself is recorded once.
Source: PDF pp.4–6. -/
abbrev SymmetricFrequency (n : ℕ) :=
  (shape : Finset (Fin n × Fin n)) × (YoungEndpointPaths n shape × YoungEndpointPaths n shape)

/-- Column minus row, fixing the sign of Young's orthogonal coefficients. -/
def boundedBoxContent {n : ℕ} (b : Fin n × Fin n) : ℤ :=
  (b.2.val : ℤ) - (b.1.val : ℤ)

/-- The Young orthogonal matrix of the adjacent transposition (i,i+1), with
row U and column T. Same-row/column cases precede division; the mixed case
has positive square root and r=content(i+1)-content(i).
Source: named Young orthogonal realization, PDF pp.5,8; coefficient convention
is the accepted Support21.P07.youngActionCoefficient, written out locally. -/
def youngAdjacent {n : ℕ} (shape : Finset (Fin n × Fin n)) (i : Fin n) :
    Matrix (YoungEndpointPaths n shape) (YoungEndpointPaths n shape) ℂ := fun U T =>
  let a := T.val.val i
  let b := T.val.val (nextIndex i)
  let r : ℝ := ((boundedBoxContent b - boundedBoxContent a : ℤ) : ℝ)
  if a.1 = b.1 then (if U = T then 1 else 0)
  else if a.2 = b.2 then (if U = T then -1 else 0)
  else if U = T then (r⁻¹ : ℝ)
  else if U.val.val = T.val.val ∘ Equiv.swap i (nextIndex i) then
    (Real.sqrt (1 - r⁻¹ ^ 2) : ℝ)
  else 0

/-- The chosen coset product, largest subgroup first: the level-i factor is
s_digit ... s_(i-1). Source: input encoding p.6 and point stabilizers p.8. -/
def symmetricWord {n : ℕ} (x : SymmetricCosetDigits n) : List (Fin n) :=
  (List.finRange n).reverse.flatMap fun level =>
    (List.finRange n).filter fun j => decide ((x level).val ≤ j.val ∧ j.val < level.val)

/-- The actual permutation specified by the source transversal digits. -/
def symmetricElement {n : ℕ} (x : SymmetricCosetDigits n) : Equiv.Perm (Fin n) :=
  ((symmetricWord x).map fun i => Equiv.swap i (nextIndex i)).prod

/-- The representation matrix is computed from that same word, in the fixed
Young orthogonal basis, before any implementation is quantified. -/
def symmetricMatrix {n : ℕ} (x : SymmetricCosetDigits n)
    (shape : Finset (Fin n × Fin n)) :
    Matrix (YoungEndpointPaths n shape) (YoungEndpointPaths n shape) ℂ :=
  ((symmetricWord x).map (youngAdjacent shape)).prod

/-- Normalized plus-sign Fourier transform: no conjugation or inverse g.
The representation dimension is the number of tableaux of its shape.
Source: Definition 1, PDF p.3; symmetric application, pp.5,8. -/
def symmetricFourier {n : ℕ} (f : SymmetricCosetDigits n → ℂ)
    (y : SymmetricFrequency n) : ℂ :=
  (Real.sqrt ((Fintype.card (YoungEndpointPaths n y.1) : ℝ) / (n.factorial : ℝ)) : ℂ) *
    ∑ x, f x * symmetricMatrix x y.1 y.2.1 y.2.2

/-- Binary encoding of the chosen transversal digits. -/
def symmetricInputCode (n q : ℕ) (x : SymmetricCosetDigits n) : Qubits q :=
  natToBits q (packDigits (Nat.clog 2 (n + 1)) (List.ofFn fun i => (x i).val))

/-- Each tableau is encoded by its successive row/column coordinates.
The shape is recoverable from either tableau and is not independently chosen. -/
def tableauDigits {n : ℕ} (T : BoundedYoungPath n) : List ℕ :=
  (List.ofFn fun i => [((T.val i).1).val, ((T.val i).2).val]).flatten

/-- Fixed output encoding of the two paths. Extra wires are zero. -/
def symmetricOutputCode (n q : ℕ) (y : SymmetricFrequency n) : Qubits q :=
  natToBits q (packDigits (Nat.clog 2 (n + 1))
    (tableauDigits y.2.1.val ++ tableauDigits y.2.2.val))

/-- A tableau's shape is computed from its boxes, never from a free label. -/
example {n : ℕ} (T : BoundedYoungPath n) :
    youngPathEndpoint T = Finset.univ.image T.val := rfl

/-- The empty word evaluates to the identity matrix on every shape sector. -/
example {n : ℕ} (shape : Finset (Fin n × Fin n)) :
    (([] : List (Fin n)).map (youngAdjacent shape)).prod = 1 := rfl

/-- Coordinates (-1)^s x_n^u_n ... x_1^u_1, including the central sign.
Source: finite Clifford monomial groups, PDF p.8. -/
abbrev CliffordElement (n : ℕ) := Bool × Qubits n

/-- The crossing sign for descending monomials: a left x_i crosses a right
x_j exactly when i<j. This fixes the actual group law, including -1. -/
def cliffordCross {n : ℕ} (u v : Qubits n) : Bool :=
  decide (Odd (∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ u i = true ∧ v j = true then (1 : ℕ) else 0))

/-- Multiplication of signed ordered monomials. -/
def cliffordMul {n : ℕ} (g h : CliffordElement n) : CliffordElement n :=
  (Bool.xor (Bool.xor g.1 h.1) (cliffordCross g.2 h.2),
    fun i => Bool.xor (g.2 i) (h.2 i))

/-- Scalar corresponding to a central sign bit. -/
def centralSignScalar (b : Bool) : ℂ := if b then -1 else 1

/-- Pauli matrices used only to specify the based irreducibles explicitly. -/
def matrixX : Matrix Bool Bool ℂ := fun r s => if r = s then 0 else 1

/-- The Y sign fixes the phase convention of the adapted Clifford rows. -/
def matrixY : Matrix Bool Bool ℂ := fun r s =>
  if r = s then 0 else if r then Complex.I else -Complex.I

/-- The first Clifford generator is diagonal in its adapted row basis. -/
def matrixZ : Matrix Bool Bool ℂ := fun r s =>
  if r = s then centralSignScalar r else 0

/-- Even rank has one nonlinear irrep; odd rank has two. -/
abbrev CliffordSector (n : ℕ) := {b : Bool // n % 2 = 1 ∨ b = false}

/-- The explicit adapted irreducible generators are Y^r Z and Y^r X on
successive tensor factors; at odd rank the last is either sign of Y^(tensor m).
Thus restriction to the earlier even level repeats literally equal blocks,
while the next odd level is selected by the last row bit. Source: p.8. -/
def cliffordGenerator {n : ℕ} (sector : CliffordSector n) (i : Fin n) :
    Matrix (Qubits (n / 2)) (Qubits (n / 2)) ℂ := fun r s =>
  if i.val < 2 * (n / 2) then
    ∏ a : Fin (n / 2),
      if a.val < i.val / 2 then matrixY (r a) (s a)
      else if a.val = i.val / 2 then
        (if i.val % 2 = 0 then matrixZ else matrixX) (r a) (s a)
      else if r a = s a then 1 else 0
  else centralSignScalar sector.val * ∏ a : Fin (n / 2), matrixY (r a) (s a)

/-- All 2^n linear characters, and all matrix entries of the nonlinear
irrep(s). No multiplicity edge is identified with another. Source: p.8. -/
abbrev CliffordFrequency (n : ℕ) :=
  Qubits n ⊕ (CliffordSector n × Qubits (n / 2) × Qubits (n / 2))

/-- The based matrix element at an actual signed monomial. The sign acts
trivially in the linear characters and as -I in the nonlinear sectors. -/
def cliffordCoefficient {n : ℕ} (y : CliffordFrequency n) (g : CliffordElement n) : ℂ :=
  match y with
  | .inl v => ∏ i : Fin n, if g.2 i then centralSignScalar (v i) else 1
  | .inr t => centralSignScalar g.1 *
      ((((List.finRange n).reverse.filter fun i => g.2 i).map
        (cliffordGenerator t.1)).prod) t.2.1 t.2.2

/-- Definition 1's dimension factor for each Clifford Fourier row. -/
def cliffordDimension {n : ℕ} : CliffordFrequency n → ℕ
  | .inl _ => 1
  | .inr _ => 2 ^ (n / 2)

/-- The source's normalized plus Fourier transform of the signed monomial
coordinates, whose group order is 2^(n+1). Source: PDF pp.3,8. -/
def cliffordFourier {n : ℕ} (f : CliffordElement n → ℂ) (y : CliffordFrequency n) : ℂ :=
  (Real.sqrt ((cliffordDimension y : ℝ) / (2 ^ (n + 1) : ℝ)) : ℂ) *
    ∑ g, f g * cliffordCoefficient y g

/-- Top-down monomial tower coordinates with the central sign at the bottom. -/
def cliffordInputCode (n q : ℕ) (g : CliffordElement n) : Qubits q :=
  natToBits q ((if g.1 then 2 ^ n else 0) + bitsToNat g.2)

/-- Character sectors followed by nonlinear block/row/column sectors. -/
def cliffordOutputCode (n q : ℕ) (y : CliffordFrequency n) : Qubits q :=
  natToBits q (match y with
    | .inl v => bitsToNat v
    | .inr t => 2 ^ n + (if t.1.val then 2 ^ (2 * (n / 2)) else 0) +
        bitsToNat t.2.1 * 2 ^ (n / 2) + bitsToNat t.2.2)

/-- The central sign is a nontrivial scalar, even though linear characters
kill it. This distinguishes the source group from its Abelian quotient. -/
example : centralSignScalar true = -1 ∧ centralSignScalar false = 1 := ⟨rfl, rfl⟩

/-- One concrete phase convention in the nonlinear adapted basis. -/
example : matrixY false true = -Complex.I := rfl

/-- All four one-dimensional characters, and the row/column entries of the
n-1 two-dimensional induced irreducibles. Source: cyclic subgroup, p.10. -/
abbrev QuaternionFrequency (n : ℕ) :=
  (Bool × Bool) ⊕ (Fin (n - 1) × Bool × Bool)

/-- The plus-sign cyclic character phase, not its complex conjugate.
Used only with N=2n>0 in the quaternion theorem. Source: Definition 1, p.3. -/
def quaternionCyclicPhase (N k j : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * (k : ℝ) * (j : ℝ) / (N : ℝ)) : ℝ) * Complex.I)

/-- Scalar of gamma in the character whose a-value is (-1)^e.
Its square is (-1)^(ne), including odd n; the second bit chooses the root. -/
def quaternionCharacterX (n : ℕ) (e b : Bool) : ℂ :=
  centralSignScalar b * (if e = true ∧ Odd n then Complex.I else 1)

/-- The source square root C(gamma), before the separate orbit permutation. -/
def quaternionTwiddle (k : ℕ) : ℂ := if Even k then 1 else Complex.I

/-- Complete fixed cyclic-subgroup-adapted matrix coefficients. For the
2D sector k=1,...,n-1, a is diag(z,z^-1) and gamma is C_k times the swap,
where C_k=1 for even k and C_k=i for odd k, as on source p.10.
The orbit permutation and the nonsplit square gamma^2=a^n are retained;
the scalar C(gamma) is not substituted for the whole induced matrix.
Source: PDF p.10; QuaternionGroup uses constructors a(j), xa(j)=gamma*a^j. -/
def quaternionCoefficient {n : ℕ} (y : QuaternionFrequency n)
    (g : QuaternionGroup n) : ℂ :=
  match y with
  | .inl eb =>
    match g with
    | .a j => centralSignScalar eb.1 ^ j.val
    | .xa j => quaternionCharacterX n eb.1 eb.2 * centralSignScalar eb.1 ^ j.val
  | .inr t =>
    let z := quaternionCyclicPhase (2 * n) (t.1.val + 1)
    match g with
    | .a j => if t.2.1 = t.2.2 then
        (if t.2.1 then star (z j.val) else z j.val) else 0
    | .xa j => if t.2.1 = t.2.2 then 0 else
        quaternionTwiddle (t.1.val + 1) * (if t.2.1 then z j.val else star (z j.val))

/-- The odd character uses the source scalar i, not an entire scalar irrep. -/
example : quaternionTwiddle 1 = Complex.I := by
  norm_num [quaternionTwiddle]

/-- The irreducible dimension entering the square-root normalization. -/
def quaternionDimension {n : ℕ} : QuaternionFrequency n → ℕ
  | .inl _ => 1
  | .inr _ => 2

/-- The normalized plus QFT of the actual Mathlib QuaternionGroup.
Source: Definition 1 p.3 and the general-n application p.10. -/
def quaternionFourier {n : ℕ} [NeZero n] (f : QuaternionGroup n → ℂ)
    (y : QuaternionFrequency n) : ℂ :=
  (Real.sqrt ((quaternionDimension y : ℝ) / (4 * n : ℝ)) : ℂ) *
    ∑ g, f g * quaternionCoefficient y g

/-- Source cyclic-coset encoding: a(j) has code j, gamma*a(j) code 2n+j. -/
def quaternionInputCode (n q : ℕ) : QuaternionGroup n → Qubits q
  | .a j => natToBits q j.val
  | .xa j => natToBits q (2 * n + j.val)

/-- Fixed character/block/row/column ordering, with no arbitrary relabeling. -/
def quaternionOutputCode (n q : ℕ) (y : QuaternionFrequency n) : Qubits q :=
  natToBits q (match y with
    | .inl eb => (if eb.1 then 2 else 0) + (if eb.2 then 1 else 0)
    | .inr t => 4 + 4 * t.1.val + (if t.2.1 then 2 else 0) + (if t.2.2 then 1 else 0))

/-- Q8 has the nonsplit square gamma^2=a^2, not gamma^2=1. -/
example : (QuaternionGroup.xa (0 : ZMod 4) : QuaternionGroup 2) *
    QuaternionGroup.xa 0 = QuaternionGroup.a 2 := by
  rw [QuaternionGroup.xa_mul_xa]
  congr 1

end QAlgorithms.Papers.Independent.Intakenext100.P78


