-- Prove2me | Definitions.Def_GL2QFT_Codes
-- name    : GL2QFT_Codes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:20.856269+00:00
-- url     : https://prove2.me/theorems/9e7724c2-2926-4e19-af37-e5760502df5e
-- title:
--   Binary codes: the data $D$, group elements, Fourier labels, and the tagged field register
-- statement:
--   The fixed classical encodings that connect the abstract transforms to qubit registers. All codes depend on the data $D$ only, never on the accuracy or on a circuit.
--
--   1. **Data code.** $D$ is written in self-delimiting binary: $p$, $r$, the coefficients of $f$, the digits of the coefficients of $F$ and the digits of $h$. Its length is $O(\log q)$.
--   2. **Input code of $\mathrm{GL}_2(\mathbb F_q)$.** $g=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ is stored as its entries $a,b,c,d$, each as $r$ base-$p$ digits in the polynomial basis, each digit in $\lceil\log_2p\rceil$ bits.
--   3. **Output code of $\mathfrak F_G$.** The label $(\mu,i,j)$ is stored as five fixed-width fields: a family tag, two label parameters, the row index $i$ and the column index $j$.
--   4. **Tagged register** (§6.4.1). A field register holds either $|a\rangle_+$ ($a\in\mathbb F_q$ in the polynomial basis, regime flag $0$) or $|g^d\rangle_\times$ (the exponent $d$, regime flag $1$); $|0\rangle_+$ is the zero sentinel. The multiplicative domain is $\{|0\rangle_+\}\cup\{|g^d\rangle_\times\}$.
--   5. **Codes for $B$ and for the $A_\gamma$ block.** $\mathfrak F_B$ reads $|a\rangle_\times|d\rangle_\times|b\rangle_+$ and writes $(\lambda,i,j)$ in five fields; the $A_\gamma$ block reads $|\gamma\rangle|c\rangle$ with $|c_\infty\rangle\leftrightarrow|0\rangle_+$, $|c_\alpha\rangle\leftrightarrow|\alpha\rangle_\times$, and writes $|\gamma\rangle|\mu\rangle$.
--
--   The codes of items 2 and 3 are injective (proved in the mission's verification file), so an implementation cannot merge labels.
--
--   **Formalization Note** The paper leaves the bit layout implicit (Remark 2.3). Any two layouts that are polynomial-time invertible differ by a reversible polynomial-time relabeling, so the choice does not affect the statements' strength. The data code is binary: a unary code of $p$ would make polynomial time vacuous.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Remark 2.3 p.14; Remark 6.3 p.34; §6.4.1 p.41 (PDF p.42, tagged register, (117)–(118)); §6.4.2 p.43 (registers of F_B); (143) p.46 (source register of A_γ); proof of Theorem 6.1 p.47

import Definitions.Def_GL2QFT_QFT
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

noncomputable section

open Classical

namespace GL2QFT

open QAlgorithms QAlgorithms.Complexity

/-- Fixed-width packing of `m` natural numbers into `m · W` bits: wire `i` carries bit `i mod W`
(least significant first) of the field `⌊i / W⌋`. Injective on fields `< 2^W`. -/
def packNat (m W : ℕ) (v : Fin m → ℕ) : Qubits (m * W) :=
  fun i => Nat.testBit (v ⟨i.val / W, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)⟩)
    (i.val % W)

/-- Zero padding: a bit string on `m` wires placed on the first `m` of `n` wires, the remaining
wires `false` (`|0⟩`). Used with `m ≤ n` (the clean ancillas). -/
def padTo (n : ℕ) {m : ℕ} (s : Qubits m) : Qubits n :=
  fun i => if h : i.val < m then s ⟨i.val, h⟩ else false

namespace FieldData

variable (D : FieldData)

/-- Bits per base-`p` digit: `⌈log₂ p⌉`. -/
def digitW : ℕ := Nat.clog 2 D.p

/-- Bits per label field: `⌈log₂(q²)⌉`, enough for every exponent label (`< q² − 1`), every digit
(`< p`) and every basis or family index (`≤ q`). -/
def labW : ℕ := Nat.clog 2 (D.q ^ 2)

/-- The `j`-th coordinate of `x ∈ F_q` in the polynomial basis `1, X, …, X^{r−1}` of
`F_p[X]/(f)`, as an integer in `[0, p−1]`. -/
def digit (x : D.Fq) (j : ℕ) : ℕ := ((AdjoinRoot.modByMonicHom D.f_monic x).coeff j).val

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Remark 6.3, p.34: the classical data `D` as
a binary string (self-delimiting binary `encBin` for every number): `p`, `r`, the `r+1`
coefficients of `f`, the `3 · r` digits of the coefficients of `F`, and the `2 · r` digits of `h`
in the basis `1, Y` of `F_q[Y]/(F)`.

**Formalization Note** The code is binary, so its length is `O(r log p) = O(log q)`; a unary
code of `p` would make "polynomial time" vacuous. Uniformity is relative to this code
(Remark 6.3: "Uniformity of the circuit should be understood relative to the supplied data `D`"). -/
def encData : Str :=
  LocalHamiltonian.encBin D.p ++ LocalHamiltonian.encBin D.r ++
    ((List.range (D.r + 1)).flatMap fun j => LocalHamiltonian.encBin (D.f.coeff j).val) ++
    ((List.range 3).flatMap fun j =>
      (List.range D.r).flatMap fun l => LocalHamiltonian.encBin (D.digit (D.F.coeff j) l)) ++
    ((List.range 2).flatMap fun j =>
      (List.range D.r).flatMap fun l =>
        LocalHamiltonian.encBin (D.digit ((AdjoinRoot.modByMonicHom D.F_monic D.h).coeff j) l))

/-- The input code of `GL₂(F_q)`: `g = (a b; c d)` is stored as its four entries `a, b, c, d` in this
order, each as its `r` base-`p` digits in the polynomial basis, each digit in `⌈log₂ p⌉` bits
(the proof of Theorem 6.1, p.47, reads `g` from its entries). Field `e·r + j` is digit `j` of
entry `e` (`e = 0, 1, 2, 3` for `(0,0), (0,1), (1,0), (1,1)`). -/
def inCode (g : D.G) : Qubits (4 * D.r * D.digitW) :=
  packNat (4 * D.r) D.digitW fun idx =>
    D.digit ((g : Matrix (Fin 2) (Fin 2) D.Fq)
      ⟨idx.val / D.r / 2 % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨idx.val / D.r % 2, Nat.mod_lt _ (by norm_num)⟩)
      (idx.val % D.r)

/-- The index of a basis label of `St_α`: `|v^⊥⟩ ↦ 0`, `|w_δ⟩ ↦ δ + 1`. -/
def stIdx : Option D.Lab → ℕ
  | none => 0
  | some δ => δ.val + 1

/-- The index of a basis label of `I_{α,β}`: `|∞⟩ ↦ 0`, `|v₀⟩ ↦ 1`, `|w_δ⟩ ↦ δ + 2`. -/
def psIdx : Option (Option D.Lab) → ℕ
  | none => 0
  | some none => 1
  | some (some δ) => δ.val + 2

/-- The four label fields `[family tag, parameter 1, parameter 2]` of an irrep of `GL₂(F_q)`:
`det α ↦ [0, α, 0]`, `st α ↦ [1, α, 0]`, `ps (α, β) ↦ [2, α, β]`, `cusp k ↦ [3, k, 0]`. -/
def irrFields : D.Irr → Fin 3 → ℕ
  | .inl α => ![0, α.val, 0]
  | .inr (.inl α) => ![1, α.val, 0]
  | .inr (.inr (.inl ab)) => ![2, ab.1.1.val, ab.1.2.val]
  | .inr (.inr (.inr k)) => ![3, k.1.val, 0]

/-- The index of a basis label of an irrep of `GL₂(F_q)` (see `stIdx`, `psIdx`; `det`: `0`;
`cusp`: `δ`). -/
def basIdx : (μ : D.Irr) → D.Bas μ → ℕ
  | .inl _ => fun _ => 0
  | .inr (.inl _) => fun i => D.stIdx i
  | .inr (.inr (.inl _)) => fun i => D.psIdx i
  | .inr (.inr (.inr _)) => fun i => (show D.Lab from i).val

/-- The output code of `F_G`: the label `(μ, i, j)` as five fields of `⌈log₂(q²)⌉` bits,
`[family tag, parameter 1, parameter 2, row index i, column index j]` (`irrFields`, `basIdx`).
It depends on `D` only (never on `ε` or on the circuit) and is injective. -/
def outCode (o : D.OutLabel) : Qubits (5 * D.labW) :=
  packNat 5 D.labW
    ![D.irrFields o.1 0, D.irrFields o.1 1, D.irrFields o.1 2, D.basIdx o.1 o.2.1, D.basIdx o.1 o.2.2]

/-- arXiv:2608.28573, §6.4.1, p.41 (PDF p.42): the tagged field register. `inl a` is `|a⟩₊`,
`a ∈ F_q` stored in the polynomial basis (regime flag `0`); `inr d` is `|g^d⟩×`, a nonzero element
(or a character label) stored by its exponent `d ∈ Z/(q−1)Z` (regime flag `1`). `|0⟩₊ = inl 0` is the
zero sentinel. -/
abbrev TagReg : Type := D.Fq ⊕ D.Lab

/-- The code of the tagged register: `r + 1` fields of `⌈log₂(q²)⌉` bits, `[flag, …]`:
`inl a ↦ [0, digit₀ a, …, digit_{r−1} a]`, `inr d ↦ [1, d, 0, …, 0]`. -/
def tagCode : D.TagReg → Qubits ((D.r + 1) * D.labW)
  | .inl a => packNat (D.r + 1) D.labW fun j => if j.val = 0 then 0 else D.digit a (j.val - 1)
  | .inr d => packNat (D.r + 1) D.labW fun j => if j.val = 0 then 1 else if j.val = 1 then d.val else 0

/-- The multiplicative domain of the tagged register (§6.4.1, p.41; (120), (122)): `none = |0⟩₊`
(the zero sentinel, "`α = 0`" in (122)) and `some d = |g^d⟩×` (a nonzero field element, or the
character label `d`; `some 0` is the trivial character, "`α = 1`"). -/
def xEmb : Option D.Lab → D.TagReg
  | none => .inl 0
  | some d => .inr d

/-- The input code of `F_B` (§6.4.2, p.43): the registers `|a⟩×|d⟩×|b⟩₊` for
`g = (1 b; 0 1)(a 0; 0 d)`: `a`, `d` by their exponents and `b` in the polynomial basis, each a
tagged register. -/
def bInCode (x : D.BElt) : Qubits ((D.r + 1) * D.labW + (D.r + 1) * D.labW + (D.r + 1) * D.labW) :=
  Fin.append (Fin.append (D.tagCode (.inr (D.dlogLab (x.1 : D.Fq))))
    (D.tagCode (.inr (D.dlogLab (x.2.1 : D.Fq))))) (D.tagCode (.inl x.2.2))

/-- The output code of `F_B`: five fields `[tag, p₁, p₂, row, column]`: `χ_{α,β} ↦ [0, α, β, 0, 0]`,
`ρ_γ` with row `δ` and column `δ'` `↦ [1, γ, 0, δ, δ']`. -/
def bOutCode : D.BOutLabel → Qubits (5 * D.labW)
  | ⟨.inl ab, _, _⟩ => packNat 5 D.labW ![0, ab.1.val, ab.2.val, 0, 0]
  | ⟨.inr γ, i, j⟩ =>
      packNat 5 D.labW ![1, γ.val, 0, (show D.Lab from i).val, (show D.Lab from j).val]

/-- The code of a pair `(γ, μ)` of a character label and an irrep label (output of the `A_γ`
block, coherent in `γ`): four fields `[γ, family tag, parameter 1, parameter 2]`. -/
def gammaIrrCode (x : D.Lab × D.Irr) : Qubits (4 * D.labW) :=
  packNat 4 D.labW ![x.1.val, D.irrFields x.2 0, D.irrFields x.2 1, D.irrFields x.2 2]

/-- The code of a pair `(γ, c)` (input of the `A_γ` block): the label `γ` in one field, followed by
the tagged register holding `c` (`none = |c_∞⟩ ↔ |0⟩₊`, `some α = |c_α⟩ ↔ |α⟩×`, p.46). -/
def gammaInCode (x : D.Lab × Option D.Lab) : Qubits (1 * D.labW + (D.r + 1) * D.labW) :=
  Fin.append (packNat 1 D.labW ![x.1.val]) (D.tagCode (D.xEmb x.2))

end FieldData

end GL2QFT


