-- Prove2me | Definitions.Def_GL2QFT_Circuits_Combinators
-- name    : GL2QFT_Circuits_Combinators
-- status  : Definition
-- author  : @dmitry
-- created : 2026-11-22T04:37:09.913807+00:00
-- url     : https://prove2.me/theorems/371b3faf-6e42-47bf-b8cc-179bb9d8f16b
-- title:
--   GL2QFT circuit combinators, encodings, and finite-field FT matrices
-- statement:
--   Shared circuit-rewiring, register-coding, and operator-matrix combinators over the Clifford+$T$ elementary gate set $\{H, S, T, X, \mathrm{CNOT}\}$ for modular uniform quantum-circuit synthesis in the $\mathrm{GL}_2(\mathbb{F}_q)$ QFT formalization.
--
--   Specifically, for an $n$-qubit Clifford+$T$ instruction list $c$, `circInv c` builds its exact adjoint using $H^\dagger = H$, $X^\dagger = X$, $\mathrm{CNOT}^\dagger = \mathrm{CNOT}$, $S^\dagger = S^3$, and $T^\dagger = T^7$. Wire relabeling (`mapInstr`, `mapCirc`, `shiftEmb`), register concatenation (`appendCode`, `boolAppCode`), and block/permutation operator constructors (`permMat`, `frameMat`, `frameMatRight`, `ctrlMat`, `subMat`) support sequential, parallel, controlled, and branch composition of `UniformlyImplementsOn` statements.
--
--   The module also defines self-delimiting signed dyadic encodings (`encSignedNat`, `encDyadicC`, `encU2Approx`, `dyadicC`, `IsPolyApproxU2`) for uniform $U(2)$ Solovay–Kitaev synthesis, together with the target operator matrices `phiFplus`, `phiFmult`, `phiExp`, `phiLog`, the tagged nontriviality code `gammaTaggedCode`, and the intermediate $F_B$ relabeling `fbOutPerm` / `bMidCode`.
--
--   **Formalization Note** Built solely on top of `Definitions.Def_GL2QFT_Uniform` (`GL2QFT.Circuits` namespace) so that downstream uniformity combinators and bridge theorems import a small, cached interface.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, Section 6.4 (pp. 41-47, Lemma 6.8, Theorem 6.10, eqs. (117)-(124))

import Definitions.Def_GL2QFT_Uniform

set_option autoImplicit false

noncomputable section

open Classical

namespace GL2QFT
namespace Circuits

open GL2QFT QAlgorithms QAlgorithms.Complexity

/-- Exact inverse of a single Clifford+T instruction (`S† = S^3`, `T† = T^7`). -/
def instrInv {n : ℕ} : Instr n → List (Instr n)
  | .h i => [.h i]
  | .s i => [.s i, .s i, .s i]
  | .t i => [.t i, .t i, .t i, .t i, .t i, .t i, .t i]
  | .x i => [.x i]
  | .cnot i j hij => [.cnot i j hij]

/-- Exact adjoint circuit over `{H, S, T, X, CNOT}` implementing `(circUnitary c)ᴴ`. -/
def circInv {n : ℕ} (c : List (Instr n)) : List (Instr n) :=
  (c.reverse.map instrInv).flatten

/-- Relabel wires of a single instruction along a wire embedding `e : Fin m ↪ Fin n`. -/
def mapInstr {m n : ℕ} (e : Fin m ↪ Fin n) : Instr m → Instr n
  | .h i => .h (e i) | .s i => .s (e i) | .t i => .t (e i) | .x i => .x (e i)
  | .cnot i j hij => .cnot (e i) (e j) (fun h => hij (e.injective h))

/-- Relabel all wires of a circuit along `e : Fin m ↪ Fin n`. -/
def mapCirc {m n : ℕ} (e : Fin m ↪ Fin n) (c : List (Instr m)) : List (Instr n) :=
  c.map (mapInstr e)

/-- Contiguous slice embedding `i ↦ off + i` from `Fin m` into `Fin n`. -/
def shiftEmb (off m n : ℕ) (h : off + m ≤ n) : Fin m ↪ Fin n :=
  ⟨fun i => ⟨off + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt off) h⟩,
    fun _ _ hab => Fin.ext (Nat.add_left_cancel (congrArg Fin.val hab))⟩

/-- Tensor product of two register codes on `m + n` wires. -/
def appendCode {X Y : Type} {m n : ℕ} (cx : X → Qubits m) (cy : Y → Qubits n) :
    X × Y → Qubits (m + n) := fun p => Fin.append (cx p.1) (cy p.2)

/-- Prepend one Boolean control wire in front of an `m`-wire register code. -/
def boolAppCode {X : Type} {m : ℕ} (cx : X → Qubits m) : Bool × X → Qubits (1 + m) :=
  fun p => Fin.append (fun (_ : Fin 1) => p.1) (cx p.2)

/-- Tagged disjoint-union register code on `1 + max m₀ m₁` wires (`false` for `.inl`, `true` for `.inr`). -/
def sumCode {X₀ X₁ : Type} {m₀ m₁ : ℕ} (c₀ : X₀ → Qubits m₀) (c₁ : X₁ → Qubits m₁) :
    X₀ ⊕ X₁ → Qubits (1 + max m₀ m₁)
  | .inl x => Fin.append (fun (_ : Fin 1) => false) (padTo (max m₀ m₁) (c₀ x))
  | .inr x => Fin.append (fun (_ : Fin 1) => true) (padTo (max m₀ m₁) (c₁ x))

/-- Isometry/permutation matrix sending `x ↦ f x`. -/
def permMat {X Y : Type} [DecidableEq Y] (f : X → Y) : Matrix Y X ℂ :=
  Matrix.of fun y x => if y = f x then 1 else 0

/-- Identity-framed block `I_A ⊗ Φ` acting on `A × X → A × Y`. -/
def frameMat {A X Y : Type} [DecidableEq A] (Φ : Matrix Y X ℂ) : Matrix (A × Y) (A × X) ℂ :=
  Matrix.of fun y x => if y.1 = x.1 then Φ y.2 x.2 else 0

/-- Right-framed block `Φ ⊗ I_B` acting on `X × B → Y × B`. -/
def frameMatRight {X Y B : Type} [DecidableEq B] (Φ : Matrix Y X ℂ) : Matrix (Y × B) (X × B) ℂ :=
  Matrix.of fun y x => if y.2 = x.2 then Φ y.1 x.1 else 0

/-- Multiplexed controlled operator `|0⟩⟨0| ⊗ Φ₀ + |1⟩⟨1| ⊗ Φ₁`. -/
def ctrlMat {X Y : Type} (Φ₀ Φ₁ : Matrix Y X ℂ) : Matrix (Bool × Y) (Bool × X) ℂ :=
  Matrix.of fun y x => if y.1 = x.1 then (if x.1 then Φ₁ y.2 x.2 else Φ₀ y.2 x.2) else 0

/-- Direct-sum block `⊕_{a ∈ A} Φ a` indexed by `A × X → A × Y`. -/
def subMat {A X Y : Type} [DecidableEq A] (Φ : A → Matrix Y X ℂ) : Matrix (A × Y) (A × X) ℂ :=
  Matrix.of fun y x => if y.1 = x.1 then Φ x.1 y.2 x.2 else 0

/-- Direct sum `Φ₀ ⊕ Φ₁` on `X₀ ⊕ X₁ → Y₀ ⊕ Y₁`. -/
def sumMat {X₀ X₁ Y₀ Y₁ : Type} (Φ₀ : Matrix Y₀ X₀ ℂ) (Φ₁ : Matrix Y₁ X₁ ℂ) :
    Matrix (Y₀ ⊕ Y₁) (X₀ ⊕ X₁) ℂ :=
  Matrix.of fun y x => match y, x with | .inl y₀, .inl x₀ => Φ₀ y₀ x₀ | .inr y₁, .inr x₁ => Φ₁ y₁ x₁ | _, _ => 0

/-- Prefix-free encoding of an integer as a sign bit followed by `encBin |z|`. -/
def encSignedNat (z : ℤ) : Str :=
  (if z < 0 then [true] else [false]) ++ LocalHamiltonian.encBin z.natAbs

/-- Prefix-free encoding of a dyadic complex numerator pair `(re, im)`. -/
def encDyadicC (z : ℤ × ℤ) : Str := encSignedNat z.1 ++ encSignedNat z.2

/-- Prefix-free encoding of a `2 × 2` dyadic complex matrix `(a00, a01, a10, a11)`. -/
def encU2Approx (a00 a01 a10 a11 : ℤ × ℤ) : Str :=
  encDyadicC a00 ++ encDyadicC a01 ++ encDyadicC a10 ++ encDyadicC a11

/-- Complex dyadic rational `(re + im * i) / 2^b`. -/
def dyadicC (b : ℕ) (z : ℤ × ℤ) : ℂ :=
  ((z.1 : ℝ) / (2 : ℝ) ^ b : ℂ) + ((z.2 : ℝ) / (2 : ℝ) ^ b : ℂ) * Complex.I

/-- Classical polynomial-time dyadic approximation oracle for a `P`-uniform family `U D ∈ U(2)`. -/
def IsPolyApproxU2 (P : FieldData → Prop) (U : FieldData → Matrix (Qubits 1) (Qubits 1) ℂ) : Prop :=
  ∃ (g : Str → Str), PolyTimeComputable g ∧
    ∀ D, P D → ∀ b : ℕ, ∃ a : Qubits 1 → Qubits 1 → ℤ × ℤ,
      g (D.encData ++ encNat b) =
        encU2Approx (a (fun _ => false) (fun _ => false)) (a (fun _ => false) (fun _ => true))
          (a (fun _ => true) (fun _ => false)) (a (fun _ => true) (fun _ => true)) ∧
      ∀ i j, ‖U D i j - dyadicC b (a i j)‖ ≤ (1 / 2 : ℝ) ^ b

/-- Additive finite-field Fourier transform matrix `𝔉₊` (Lemma 6.8 clause 1). -/
def phiFplus (D : FieldData) : Matrix D.Fq D.Fq ℂ :=
  Matrix.of fun y x => FieldData.isqrt D.q * D.psi (x * y)

/-- Multiplicative finite-field Fourier transform matrix `𝔉×` fixing `|0⟩₊` (Lemma 6.8 clause 2). -/
def phiFmult (D : FieldData) : Matrix (Option D.Lab) (Option D.Lab) ℂ :=
  Matrix.of fun out inp => match out, inp with
    | none, none => 1 | some α, some d => FieldData.isqrt (D.q - 1) * D.chi α (D.gen ^ d.val) | _, _ => 0

/-- Conversion matrix `exp_g` from multiplicative exponent labels to additive elements (Lemma 6.8 clause 3). -/
def phiExp (D : FieldData) : Matrix D.Fq (Option D.Lab) ℂ :=
  Matrix.of fun y inp => match inp with
    | none => if y = 0 then 1 else 0 | some d => if y = D.gen ^ d.val then 1 else 0

/-- Conversion matrix `log_g` from additive elements to multiplicative exponent labels (Lemma 6.8 clause 4). -/
def phiLog (D : FieldData) : Matrix (Option D.Lab) D.Fq ℂ :=
  Matrix.of fun out a => match out with
    | none => if a = 0 then 1 else 0 | some d => if a ≠ 0 ∧ D.gen ^ d.val = a then 1 else 0

/-- True iff `c : Option D.Lab` represents a nontrivial multiplicative character (`α ≠ 0`). -/
def isNontrivLab {D : FieldData} : Option D.Lab → Bool | some α => decide (α ≠ 0) | none => false

/-- Tagged multiplicative code prepending the nontriviality flag bit `isNontrivLab c`. -/
def gammaTaggedCode (D : FieldData) (c : Option D.Lab) : Qubits (1 + (D.r + 1) * D.labW) :=
  boolAppCode (fun c => D.tagCode (D.xEmb c)) (isNontrivLab c, c)

/-- Relabeling map of `U_{B,transv}` from `(α, β, η?)` to `D.BOutLabel` (`(123)–(124)`). -/
def fbOutPerm (D : FieldData) : D.Lab × D.Lab × Option D.Lab → D.BOutLabel
  | (α, β, none) => ⟨.inl (α, β), (), ()⟩ | (α, β, some η) => ⟨.inr (α + β), α - η, α⟩

/-- Intermediate 3-register tagged code `(α, β, η?)` prior to `U_{B,transv}`. -/
def bMidCode (D : FieldData) (p : D.Lab × D.Lab × Option D.Lab) :
    Qubits ((D.r + 1) * D.labW + (D.r + 1) * D.labW + (D.r + 1) * D.labW) :=
  Fin.append (Fin.append (D.tagCode (.inr p.1)) (D.tagCode (.inr p.2.1))) (D.tagCode (D.xEmb p.2.2))

/-- Canonical injection of `D.BElt` into the 3-register intermediate domain of `F_B`. -/
def bInEmb (D : FieldData) (x : D.BElt) : (Option D.Lab × Option D.Lab) × D.Fq :=
  ((some (D.dlogLab (x.1 : D.Fq)), some (D.dlogLab (x.2.1 : D.Fq))), x.2.2)

/-- Canonical injection of `D.Lab × D.Lab × Option D.Lab` into `(Option D.Lab × Option D.Lab) × Option D.Lab`. -/
def bMidInj (D : FieldData) (p : D.Lab × D.Lab × Option D.Lab) :
    (Option D.Lab × Option D.Lab) × Option D.Lab := ((some p.1, some p.2.1), p.2.2)

end Circuits
end GL2QFT


