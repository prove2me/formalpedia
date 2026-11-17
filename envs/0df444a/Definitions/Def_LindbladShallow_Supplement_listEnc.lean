-- Prove2me | Definitions.Def_LindbladShallow_Supplement_listEnc
-- name    : LindbladShallow_Supplement_listEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:19:41.89321+00:00
-- url     : https://prove2.me/theorems/beb68139-a076-4dae-b2ee-f5e86ddff985
-- title:
--   List-encoded owner environment blocks, canonical lists and the common block space $K_A$ (§5.1–5.2)
-- statement:
--   Fix a valid input, a number $M$ of periods, the coarse-graining length $R$ and an owner cube $C$.
--
--   1. The **complete owner environment blocks** of the factor $W_C$ are the assigned owner cubes $A$ with $\|A-C\|_\infty\le 3$. The **complete term list** of $A$ lists, in input order, the $P_A$ retained terms whose owner is $A$; term ordinals are $1,\dots,P_A$.
--   2. The **physical baths** of $A$ are the jump-occurrence labels $(e,m)$, $0\le m<M$, of its jump terms; a physical configuration assigns each a value in $\{0,\dots,d_E-1\}$, with $0$ the vacuum.
--   3. The **list register** of $A$ has $C_{\mathrm{cap}}$ records; each record has $w_{b,A}=\lceil\log_2(P_A+1)\rceil+\log_2 M$ label bits and $\log_2 d_E$ value bits. The label value is $o\cdot 2^{\log_2 M}+m$ with $o$ a term ordinal and $m$ a period.
--   4. A record is **legal** if it names a jump term ($1\le o\le P_A$), a period $m<M$, and a nonzero value; it is **empty** if both fields are zero. A list is **canonical** if it consists of legal records with strictly increasing labels followed by empty records. A canonical list represents the physical configuration with exactly the listed nonzero values.
--   5. The **common block space** is $K_A:=L_A\oplus P^{\mathrm{high}}_A\oplus H^{\mathrm{invalid}}_A$: every physical configuration (within the capacity, or above it), or a noncanonical register string. The inclusion $j_{P,A}$ embeds physical configurations; $j_{H,A}$ sends a canonical list to the configuration it represents and a noncanonical string to itself. The two inclusions agree on the capacity subspace.
--
--   These objects let Theorem 5.1 compare a hardware circuit acting on compressed bath lists with the physical factor acting on uncompressed baths, in one space that keeps the physical configurations above capacity.
--
--   **Formalization Note** The page leaves the bit layout of a label to the encoder; here the ordinal occupies the high bits and the period the low $\log_2 M$ bits, and labels are compared as binary numbers (bit $0$ least significant). The capacity $C_{\mathrm{cap}}$ is a parameter, chosen by the construction of Theorem 5.1. A stored value is read modulo $d_E$, which changes nothing since the field has $\log_2 d_E$ bits.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §5.1 Table 4 and text, pp.38–39; Lemma 5.2, p.40; §5.2, p.42; complete local bath set p.19

import Mathlib
import Definitions.Def_LindbladShallow_localDecomp

open scoped Matrix ComplexOrder

namespace LindbladShallow

namespace Supplement

variable {P : Params}

/-- The complete owner environment blocks of the factor `W_C` (arXiv:2610.05362, held version
sha256 8f4637ef…, §3.3, p.19 and §5.2, p.42): the assigned owner cubes `C'` with
`‖C' − C‖_∞ ≤ 3`. -/
noncomputable def blocksOf (I : Instance P) (R : ℕ) (C : Fin P.D → ℤ) : Finset (Fin P.D → ℤ) :=
  open Classical in
  (CLam I R).filter fun C' => ∀ j, |C' j - C j| ≤ 3

/-- The complete term list of owner `A` in its fixed order (input order): the retained terms whose
owner cube is `A` (§5.1, p.38: "In the owner's fixed complete term order, ordinals `1, …, P_C`
identify terms"). -/
noncomputable def ownerTerms (I : Instance P) (R : ℕ) (A : Fin P.D → ℤ) : List (Fin I.nT) :=
  open Classical in
  (List.finRange I.nT).filter fun e => decide ((I.term e).Retained ∧ owner R (I.term e) = A)

/-- The physical bath labels of owner block `A`: the jump-occurrence labels `(e, m)` whose term has
owner `A` (all periods). -/
def BathsOf (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) := {b : BJ I M // owner R (I.term b.1.1) = A}

noncomputable instance (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) : Fintype (BathsOf I M R A) := by
  classical
  unfold BathsOf
  infer_instance

noncomputable instance (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) :
    DecidableEq (BathsOf I M R A) := by
  classical
  unfold BathsOf
  infer_instance

/-- The label width `w_{b,C} = ⌈log₂(P_C + 1)⌉ + log₂ M` of owner `A` (§5.1, p.38). -/
noncomputable def wlab (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) : ℕ :=
  Nat.clog 2 ((ownerTerms I R A).length + 1) + Nat.log 2 M

/-- The constant value width `log₂ d_E = ⌈log₂(1 + µ∗)⌉` (§2.3, p.12): a bath value `0, …, d_E − 1`
is stored in this many bits. -/
def wval (P : Params) : ℕ := Nat.clog 2 (1 + P.μstar)

/-- A record `B_{C,ℓ}` of the list register of owner `A`: label bits `J_{C,ℓ,0:w_b−1}` and value bits
`L_{C,ℓ}` (Table 4, p.38). -/
abbrev Rec (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) :=
  (Fin (wlab I M R A) → Bool) × (Fin (wval P) → Bool)

/-- The environment block of owner `A` with `Ccap` records (Table 4, p.38). -/
abbrev HwBlock (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) (Ccap : ℕ) :=
  Fin Ccap → Rec I M R A

/-- The binary value `Σ_i 2^i f_i` of a bit string (bit `0` least significant). -/
def bitsVal {w : ℕ} (f : Fin w → Bool) : ℕ := ∑ i, if f i then 2 ^ (i : ℕ) else 0

/-- The numeric label of bath `(e, m)` of owner `A`: `ord(e) · 2^{log₂ M} + m`, with
`ord(e) ∈ {1, …, P_A}` the one-based ordinal of `e` in the owner's complete term list (the ordinal
occupies the high label bits, the period the low `log₂ M` bits). -/
noncomputable def bathLabel (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) (b : BathsOf I M R A) : ℕ :=
  ((ownerTerms I R A).idxOf b.1.1.1 + 1) * 2 ^ Nat.log 2 M + b.1.1.2.val

/-- A legal occupied record (§5.1, p.38; Lemma 5.2, p.40): its label names a term ordinal
`1 ≤ o ≤ P_A` of a jump term and a period `m < M`, and its value is nonzero. -/
def RecLegal (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) (rc : Rec I M R A) : Prop :=
  let o := bitsVal rc.1 / 2 ^ Nat.log 2 M
  let m := bitsVal rc.1 % 2 ^ Nat.log 2 M
  1 ≤ o ∧ (∃ h : o - 1 < (ownerTerms I R A).length,
    (I.term ((ownerTerms I R A).get ⟨o - 1, h⟩)).IsJump) ∧ m < M ∧ bitsVal rc.2 ≠ 0

/-- An empty record: both fields zero. -/
def RecEmpty (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) (rc : Rec I M R A) : Prop :=
  (∀ i, rc.1 i = false) ∧ ∀ i, rc.2 i = false

/-- A canonical list (§5.1, p.38): some `k ≤ C_cap` legal occupied records with strictly increasing
labels, followed by records with both fields zero. -/
def Canonical (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) {Ccap : ℕ}
    (s : HwBlock I M R A Ccap) : Prop :=
  ∃ k ≤ Ccap, (∀ i : Fin Ccap, (i : ℕ) < k → RecLegal I M R A (s i)) ∧
    (∀ i : Fin Ccap, k ≤ (i : ℕ) → RecEmpty I M R A (s i)) ∧
    ∀ i i' : Fin Ccap, i < i' → (i' : ℕ) < k → bitsVal (s i).1 < bitsVal (s i').1

/-- The physical bath configuration represented by a list: bath `b` carries the value of the legal
record whose label is `b`'s label, and the vacuum `0` if there is none (§5.1, p.38: "a canonical list
… is identified with the physical bath configuration … that has exactly those nonzero values").

**Formalization Note** The stored value is read modulo `d_E`; since the value field has
`log₂ d_E` bits, this changes no value. -/
noncomputable def decodeBlock (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) {Ccap : ℕ}
    (s : HwBlock I M R A Ccap) : BathsOf I M R A → Fin (dEm1 P + 1) :=
  open Classical in
  fun b => if h : ∃ i, RecLegal I M R A (s i) ∧ bitsVal (s i).1 = bathLabel I M R A b then
    Fin.ofNat (dEm1 P + 1) (bitsVal (s h.choose).2) else 0

/-- The common space `K_A := L_A ⊕ P^high_A ⊕ H^invalid_A` of owner block `A` (§5.2, p.42), as a
basis: every physical bath configuration of the block (`L_A ⊕ P^high_A`: within capacity or above
it), or a noncanonical register string (`H^invalid_A`). -/
abbrev KBlock (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) (Ccap : ℕ) :=
  (BathsOf I M R A → Fin (dEm1 P + 1)) ⊕ {s : HwBlock I M R A Ccap // ¬ Canonical I M R A s}

noncomputable instance (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) (Ccap : ℕ) :
    Fintype (KBlock I M R A Ccap) := by
  classical
  infer_instance

/-- The canonical inclusion `j_{H,A}` of the list register into `K_A` (§5.2, p.42): a canonical list
goes to the physical configuration it represents, a noncanonical string to itself. (`j_{P,A}` is
`Sum.inl`.) -/
noncomputable def jH (I : Instance P) (M R : ℕ) (A : Fin P.D → ℤ) {Ccap : ℕ}
    (s : HwBlock I M R A Ccap) : KBlock I M R A Ccap :=
  open Classical in
  if h : Canonical I M R A s then Sum.inl (decodeBlock I M R A s) else Sum.inr ⟨s, h⟩

end Supplement

end LindbladShallow


