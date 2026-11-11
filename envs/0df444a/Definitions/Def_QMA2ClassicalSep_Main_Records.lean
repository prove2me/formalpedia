-- Prove2me | Definitions.Def_QMA2ClassicalSep_Main_Records
-- name    : QMA2ClassicalSep_Main_Records
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:02.722218+00:00
-- url     : https://prove2.me/theorems/36505c3a-2868-47e4-a080-d10a02851a07
-- title:
--   §6.1 — records, decompression $\mathrm{Dec}_\pm$, queries on records $Z_\pm$, $C_\pm$, $O_\pm$, $P_{\mathrm{size}}$, $P_{\mathrm{bad}}$
-- statement:
--   A **YES record** $(D,S)$ is a permutation database $D=(D_p)_{p\in[N]}$ (each $D_p$ a partial bijection on $V$, stored as entries $(p;x\mapsto y)$) together with a sign database $S\subseteq\mathcal X=\mathcal X_A\sqcup\mathcal X_B$; its size is $|D|+|S|$. A **NO record** $(\theta,D,S)$ has a NO database for $\theta$: partial bijections $D_{p,\mathcal B}$ on the nonempty blocks $\mathcal B$ of $\theta$. These records form orthonormal bases of $\mathrm{Rec}_+$ and $\mathrm{Rec}_-=\bigoplus_\theta|\theta\rangle\otimes\mathrm{Rec}_-(\theta)$; $\mathrm{Rec}_{\le R}$ is spanned by records of size at most $R$. For an entry $e$, $\partial e$ is the set of coordinates occurring an odd number of times among $x_A,x_B,y_A,y_B$.
--
--   **Decompression.** On a domain $X$ of size $s$, $\mathrm{Dec}^{\to}_x$ exchanges $|I\rangle$ and $(s-|I|)^{-1/2}\sum_{y\in X\setminus\mathrm{ran}(I)}|I\cup\{x\mapsto y\}\rangle$ for every table $I$ with $x\notin\mathrm{dom}(I)$ and is the identity on the orthogonal complement; $\mathrm{Dec}^{\leftarrow}_y$ is the same with inputs and outputs exchanged. For an address $a=(p,z,v)$, $\mathrm{Dec}_{\pm,a}$ acts on $D_p$ (YES, $X=V$) or on $D_{p,\mathcal B_\theta(v)}$ (NO), and $\mathrm{Dec}_\pm=\sum_a\mathrm{Dec}_{\pm,a}\otimes|a\rangle\langle a|$.
--
--   **Queries on records.** With the sign qubit in the Fourier basis $|\hat t\rangle=H|t\rangle$, and $e$ the entry of $D$ selected by $a$ (answer endpoint $v'_a$),
--   $$
--   Z_+|D,S\rangle|a,w,\hat t\rangle=|D,S\triangle(t\,\partial e)\rangle|a,w\oplus v'_a,\hat t\rangle,\qquad
--   Z_-|\theta,D,S\rangle|a,w,\hat t\rangle=s_\theta(x,y)^t|\theta,D,S\triangle(t\,\partial e)\rangle|a,w\oplus v'_a,\hat t\rangle,
--   $$
--   and $Z_\pm$ is the identity if no entry is selected; $C_\pm=\mathrm{Dec}_\pm Z_\pm\mathrm{Dec}_\pm$ (7).
--
--   **Oracle registers.** $\mathcal H_\pm$ have orthonormal bases indexed by $\Omega_\pm=\operatorname{supp}\mathcal D_\pm$; $|\mathcal D_+\rangle=\sum_{\omega_+}\sqrt{\mathcal D_+(\omega_+)}|\omega_+\rangle$; $O_\pm=\sum_{\omega}|\omega\rangle\langle\omega|\otimes O_\omega$. $P_{\mathrm{size}}$ projects onto $\theta\in\Theta_{\mathrm{size}}$, $P_{\mathrm{bad}}$ onto bad NO parameters, $P_{\pm,a}$ onto records containing the entry queried by $a$.
--
--   **Formalization Note** A NO database is stored as the set of its entries, all of which have both endpoints in one block of $\theta$; this is in bijection with the tuple $(D_{p,\mathcal B})$. Vectors are functions on the record basis; tensoring with a register $\mathcal E$ is the identity on $\mathcal E$ (`tensorId`, `liftQ`).
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, Section 6.1, pp. 24–27 (oracle registers, records, decompression, queries on records, Equation (7), P_size); p. 28 (P_bad); pp. 48–49 (P_{±,a})

import Definitions.Def_QMA2ClassicalSep_Main_HardDist

set_option autoImplicit false

/-!
# Section 6.1: oracle registers, records, decompression and queries on records

Grewal, Mutreja, Tomer, *A classical oracle separation between QMA and QMA(2)*, STOC 2027
submission #618, Section 6.1, pp. 24–27, and the projectors `P_size` (p. 27), `P_bad` (p. 28),
`P_{±,a}` (pp. 48–49).

Vectors are functions on an orthonormal basis; operators are matrices in that basis. A NO
permutation database `(D_{p,𝔅})` (one partial bijection per `p` and nonempty block `𝔅` of `θ`) is
stored as the set of its entries `(p; x ↦ y)`: a database whose entries all have both endpoints
in one block of `θ`; the two descriptions are in bijection.
-/

namespace QMA2ClassicalSep.Main

open Matrix

attribute [local instance] Classical.propDecidable

/-! ## Generic Hilbert-space helpers -/

/-- The Euclidean norm `‖v‖ = (Σ_i |v_i|²)^{1/2}`. -/
noncomputable def vnorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (v i))

/-- `M ⊗ 𝕀_ε`. -/
noncomputable def tensorId {α β : Type*} (ε : Type*) (M : Matrix α β ℂ) : Matrix (α × ε) (β × ε) ℂ :=
  fun i j => if i.2 = j.2 then M i.1 j.1 else 0

/-- An operator `M` on `α ⊗ Q` acting on `α ⊗ (Q ⊗ F)` as `M ⊗ 𝕀_F`. -/
noncomputable def liftQ {α β Q : Type*} (F : Type*) (M : Matrix (α × Q) (β × Q) ℂ) :
    Matrix (α × (Q × F)) (β × (Q × F)) ℂ :=
  fun i j => if i.2.2 = j.2.2 then M (i.1, i.2.1) (j.1, j.2.1) else 0

/-- `v` lies in the span of basis vectors `(r, e)` with `size r ≤ R` (the subspace `Rec_{≤R} ⊗ ℰ`). -/
def SizeLe {α ε : Type*} (size : α → ℕ) (R : ℕ) (v : α × ε → ℂ) : Prop :=
  ∀ i, R < size i.1 → v i = 0

/-! ## Entries, databases, records -/

variable {k : ℕ}

/-- A permutation-table entry `(p; x ↦ y)`. -/
abbrev Entry (k : ℕ) := PIdx k × HVtx k × HVtx k

instance (k : ℕ) : DecidableEq (Entry k) := instDecidableEqProd

/-- A coordinate `u ∈ 𝒳 = 𝒳_A ⊔ 𝒳_B` (the side is part of the coordinate). -/
abbrev HCoord (k : ℕ) := Coord (3 * k) ⊕ Coord (3 * k)

/-- A permutation database: for each `p`, the entries with index `p` form a partial bijection
(no repeated input, no repeated output). -/
def IsDatabase (D : Finset (Entry k)) : Prop :=
  ∀ e ∈ D, ∀ e' ∈ D, e.1 = e'.1 → (e.2.1 = e'.2.1 ∨ e.2.2 = e'.2.2) → e = e'

/-- The coordinates `{x_A, x_B, y_A, y_B}` of an entry. -/
def coordsE (e : Entry k) : Finset (HCoord k) :=
  {Sum.inl e.2.1.1, Sum.inr e.2.1.2, Sum.inl e.2.2.1, Sum.inr e.2.2.2}

/-- `coords(D)`: the union of the coordinates of the entries of `D`. -/
def coords (D : Finset (Entry k)) : Finset (HCoord k) := D.biUnion coordsE

/-- `∂e`: the coordinates occurring an odd number of times among `x_A, x_B, y_A, y_B`. -/
def bdry (e : Entry k) : Finset (HCoord k) :=
  symmDiff {Sum.inl e.2.1.1} {Sum.inl e.2.2.1} ∪ symmDiff {Sum.inr e.2.1.2} {Sum.inr e.2.2.2}

/-- YES records `(D, S)`: `D` a YES permutation database (a partial bijection on `V` for each
`p`), `S ⊆ 𝒳` a sign database. Basis of `Rec₊`. -/
abbrev YRec (k : ℕ) := {r : Finset (Entry k) × Finset (HCoord k) // IsDatabase r.1}

/-- NO records `(θ, D, S)`: a labeling `θ`, a NO permutation database for `θ` (entries within
blocks), and `S ⊆ 𝒳`. Basis of `Rec₋ = ⊕_θ |θ⟩ ⊗ Rec₋(θ)`. -/
abbrev NRec (k : ℕ) :=
  {r : Labeling k × Finset (Entry k) × Finset (HCoord k) //
    IsDatabase r.2.1 ∧ ∀ e ∈ r.2.1, SameBlock r.1 e.2.1 e.2.2}

noncomputable instance (k : ℕ) : Fintype (YRec k) := Subtype.fintype _
noncomputable instance (k : ℕ) : DecidableEq (YRec k) := Subtype.instDecidableEq
noncomputable instance (k : ℕ) : DecidableEq (NRec k) := Subtype.instDecidableEq
noncomputable instance (k : ℕ) : Fintype (NRec k) := Subtype.fintype _

/-- Record size `|D| + |S|`. -/
def YRec.size (r : YRec k) : ℕ := r.1.1.card + r.1.2.card

/-- Record size `|D| + |S|`. -/
def NRec.size (r : NRec k) : ℕ := r.1.2.1.card + r.1.2.2.card

/-- The empty YES record `|∅⟩` (every table empty, `S = ∅`), as a vector of `Rec₊`. -/
noncomputable def emptyRec : YRec k → ℂ := fun r => if r.1 = (∅, ∅) then 1 else 0

/-! ## Decompression -/

/-- The entry selected by an address `a = (p, z, v)`: `(p; v ↦ ·)` if `z = 0`, `(p; · ↦ v)` if
`z = 1`. -/
def Sel (a : Addr k (3 * k)) (e : Entry k) : Prop :=
  e.1 = a.1 ∧ (if a.2.1 then e.2.2 = a.2.2 else e.2.1 = a.2.2)

/-- The matrix entry `⟨D'| Dec |D⟩` of the decompression operator for address `a` on the table
of index `p` over the domain `X` (of size `s = |X|`). `Dec→_v` (`z = 0`) exchanges `|I⟩` and
`(s − |I|)^{-1/2} Σ_{y ∈ X ∖ ran I} |I ∪ {v ↦ y}⟩` for every table `I` with `v ∉ dom I`, and is
the identity on the orthogonal complement; `Dec←_v` (`z = 1`) likewise with inputs and outputs
exchanged. Here `rest D` removes the selected entry and `c` is the size of the remaining
table `I` (its entries `(p; x ↦ ·)` with `x ∈ X`). -/
noncomputable def decEntry (a : Addr k (3 * k)) (X : Finset (HVtx k))
    (D' D : Finset (Entry k)) : ℂ :=
  let hit := fun E : Finset (Entry k) => ∃ e ∈ E, Sel a e
  let rest := fun E : Finset (Entry k) => E.filter (fun e => ¬ Sel a e)
  let c := fun E : Finset (Entry k) =>
    ((rest E).filter (fun e => e.1 = a.1 ∧ e.2.1 ∈ X)).card
  let ok := fun E : Finset (Entry k) => ∀ e ∈ E, Sel a e → e.2.1 ∈ X ∧ e.2.2 ∈ X
  let s := X.card
  if hit D' ∧ hit D then
    (if D' = D then 1 - 1 / ((s : ℂ) - c D)
     else if rest D' = rest D then -1 / ((s : ℂ) - c D) else 0)
  else if hit D' then
    (if rest D' = D ∧ ok D' then 1 / (Real.sqrt ((s : ℝ) - c D) : ℂ) else 0)
  else if hit D then
    (if rest D = D' ∧ ok D then 1 / (Real.sqrt ((s : ℝ) - c D') : ℂ) else 0)
  else 0

/-- `Dec_{+,a}` on `Rec₊`: decompression on the table `D_p` (domain `V`, `s = |V| = N⁶`). -/
noncomputable def decY (a : Addr k (3 * k)) : Matrix (YRec k) (YRec k) ℂ :=
  fun r' r => if r'.1.2 = r.1.2 then decEntry a Finset.univ r'.1.1 r.1.1 else 0

/-- `Dec_{−,a}` on `Rec₋`: decompression on the table `D_{p, 𝔅_θ(v)}` (domain the block of `v`). -/
noncomputable def decN (a : Addr k (3 * k)) : Matrix (NRec k) (NRec k) ℂ :=
  fun r' r => if r'.1.1 = r.1.1 ∧ r'.1.2.2 = r.1.2.2 then
    decEntry a (blockOf r.1.1 a.2.2) r'.1.2.1 r.1.2.1 else 0

/-- `Dec± = Σ_a Dec_{±,a} ⊗ |a⟩⟨a|` on `Rec ⊗ (query register)`, with `decA a = Dec_{±,a}`. -/
noncomputable def decFull {R : Type*} (decA : Addr k (3 * k) → Matrix R R ℂ) :
    Matrix (R × QReg k (3 * k)) (R × QReg k (3 * k)) ℂ :=
  fun i j => if i.2 = j.2 then decA j.2.1 i.1 j.1 else 0

/-! ## Queries on records -/

/-- `w ⊕ u` for vertex registers. -/
def vxor {ℓ : ℕ} (w u : Vtx ℓ) : Vtx ℓ :=
  (fun i => xor (w.1 i) (u.1 i), fun i => xor (w.2 i) (u.2 i))

/-- The unique entry of `D` selected by `a`, if any. -/
noncomputable def selEntry (a : Addr k (3 * k)) (D : Finset (Entry k)) : Option (Entry k) :=
  if h : ∃ e ∈ D, Sel a e then some (Classical.choose h) else none

/-- `v'_a`: the answer vertex of the selected entry (`y` for `z = 0`, `x` for `z = 1`). -/
def answerVtx (a : Addr k (3 * k)) (e : Entry k) : HVtx k := if a.2.1 then e.2.1 else e.2.2

/-- The Hadamard gate on the sign qubit `t` of the answer register (identity elsewhere), the
change of basis `|t̂⟩ = H|t⟩`. -/
noncomputable def hadT {R : Type*} : Matrix (R × QReg k (3 * k)) (R × QReg k (3 * k)) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2.1 = j.2.1 ∧ i.2.2.1 = j.2.2.1 then
    (if i.2.2.2 && j.2.2.2 then -1 else 1) / (Real.sqrt 2 : ℂ) else 0

/-- `Z₊` in the basis `|D, S⟩|a, w, t̂⟩`:
`|D, S⟩|a, w, t̂⟩ ↦ |D, S △ (t∂e)⟩|a, w ⊕ v'_a, t̂⟩` if `D` contains the entry `e` selected by `a`,
identity otherwise. -/
noncomputable def zHatY : Matrix (YRec k × QReg k (3 * k)) (YRec k × QReg k (3 * k)) ℂ :=
  fun i' i =>
    match selEntry i.2.1 i.1.1.1 with
    | none => if i' = i then 1 else 0
    | some e =>
      if i'.1.1 = (i.1.1.1, symmDiff i.1.1.2 (if i.2.2.2 then bdry e else ∅)) ∧
          i'.2 = (i.2.1, (vxor i.2.2.1 (answerVtx i.2.1 e), i.2.2.2)) then 1 else 0

/-- `Z₋` in the basis `|θ, D, S⟩|a, w, t̂⟩`:
`|θ, D, S⟩|a, w, t̂⟩ ↦ s_θ(x, y)^t |θ, D, S △ (t∂e)⟩|a, w ⊕ v'_a, t̂⟩` for the selected entry
`e = (p; x ↦ y)`, identity otherwise. -/
noncomputable def zHatN : Matrix (NRec k × QReg k (3 * k)) (NRec k × QReg k (3 * k)) ℂ :=
  fun i' i =>
    match selEntry i.2.1 i.1.1.2.1 with
    | none => if i' = i then 1 else 0
    | some e =>
      if i'.1.1 = (i.1.1.1, i.1.1.2.1, symmDiff i.1.1.2.2 (if i.2.2.2 then bdry e else ∅)) ∧
          i'.2 = (i.2.1, (vxor i.2.2.1 (answerVtx i.2.1 e), i.2.2.2)) then
        (if i.2.2.2 then (sθ i.1.1.1 e.2.1 e.2.2 : ℂ) else 1) else 0

/-- `Z₊` in the computational basis. -/
noncomputable def zY : Matrix (YRec k × QReg k (3 * k)) (YRec k × QReg k (3 * k)) ℂ :=
  hadT (k := k) (R := YRec k) * zHatY (k := k) * hadT (k := k) (R := YRec k)

/-- `Z₋` in the computational basis. -/
noncomputable def zN : Matrix (NRec k × QReg k (3 * k)) (NRec k × QReg k (3 * k)) ℂ :=
  hadT (k := k) (R := NRec k) * zHatN (k := k) * hadT (k := k) (R := NRec k)

/-- `C₊ = Dec₊ Z₊ Dec₊`, Equation (7). -/
noncomputable def cY : Matrix (YRec k × QReg k (3 * k)) (YRec k × QReg k (3 * k)) ℂ :=
  decFull (k := k) decY * zY (k := k) * decFull (k := k) decY

/-- `C₋ = Dec₋ Z₋ Dec₋`, Equation (7). -/
noncomputable def cN : Matrix (NRec k × QReg k (3 * k)) (NRec k × QReg k (3 * k)) ℂ :=
  decFull (k := k) decN * zN (k := k) * decFull (k := k) decN

/-- `P_{+,a}`: projector onto the records whose database contains the entry queried by `a`. -/
noncomputable def projAddrY (a : Addr k (3 * k)) : Matrix (YRec k) (YRec k) ℂ :=
  Matrix.diagonal (fun r => if ∃ e ∈ r.1.1, Sel a e then 1 else 0)

/-- `P_{−,a}`: projector onto the records whose database contains the entry queried by `a`. -/
noncomputable def projAddrN (a : Addr k (3 * k)) : Matrix (NRec k) (NRec k) ℂ :=
  Matrix.diagonal (fun r => if ∃ e ∈ r.1.2.1, Sel a e then 1 else 0)

/-- `P_size = Σ_{θ ∈ Θ_size} |θ⟩⟨θ| ⊗ I` on `Rec₋`. -/
noncomputable def pSizeRec : Matrix (NRec k) (NRec k) ℂ :=
  Matrix.diagonal (fun r => if InThetaSize r.1.1 then 1 else 0)

/-! ## Oracle-parameter spaces -/

/-- `Ω₋ = supp 𝒟₋`, the basis of `ℋ₋`. (`Ω₊ = supp 𝒟₊` is all of `YESParam k`.) -/
abbrev NOSupp (k : ℕ) := {ω : NOParam k // InSuppNo ω}

noncomputable instance (k : ℕ) : Fintype (NOSupp k) := Subtype.fintype _

/-- The purified YES distribution `|𝒟₊⟩ = Σ_{ω₊} √(𝒟₊(ω₊)) |ω₊⟩` (`𝒟₊` is uniform on `Ω₊`). -/
noncomputable def purYes : YESParam k → ℂ :=
  fun _ => (Real.sqrt (1 / (Fintype.card (YESParam k) : ℝ)) : ℂ)

/-- `O₊ = Σ_{ω₊} |ω₊⟩⟨ω₊| ⊗ O_{ω₊}` (the query `U_O` of the instance in the parameter register). -/
noncomputable def oracleY :
    Matrix (YESParam k × QReg k (3 * k)) (YESParam k × QReg k (3 * k)) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2 = (yesInst j.1).queryMap j.2 then 1 else 0

/-- `O₋ = Σ_{ω₋} |ω₋⟩⟨ω₋| ⊗ O_{ω₋}`. -/
noncomputable def oracleN :
    Matrix (NOSupp k × QReg k (3 * k)) (NOSupp k × QReg k (3 * k)) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2 = (noInst j.1.1).queryMap j.2 then 1 else 0

/-- `P_size` on `ℋ₋`: projector onto parameters with `θ ∈ Θ_size`. -/
noncomputable def pSizePar : Matrix (NOSupp k) (NOSupp k) ℂ :=
  Matrix.diagonal (fun ω => if InThetaSize ω.1.2.2.2 then 1 else 0)

/-- `P_bad = Σ_{ω₋ ∈ Ω₋ ∖ Ω₋^good} |ω₋⟩⟨ω₋|`. -/
noncomputable def pBad : Matrix (NOSupp k) (NOSupp k) ℂ :=
  Matrix.diagonal (fun ω => if IsGood ω.1 then 0 else 1)

end QMA2ClassicalSep.Main


