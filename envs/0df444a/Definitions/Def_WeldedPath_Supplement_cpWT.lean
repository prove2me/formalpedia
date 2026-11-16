-- Prove2me | Definitions.Def_WeldedPath_Supplement_cpWT
-- name    : WeldedPath_Supplement_cpWT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:12:09.878753+00:00
-- url     : https://prove2.me/theorems/45568d69-b5cf-4088-9f36-121943c9ece6
-- title:
--   The ordinary compressed welded trees oracle $\mathrm{cpWT}$ (Definition 3.4)
-- statement:
--   The welded trees oracle answers a query $|l,\alpha\rangle_X|a\rangle_Y$ (a label $l\in[0,M]$, $M=2^{2n}$, a color $\alpha$, an answer string $a$ of $2n+1$ bits) with $a\oplus\sigma_{\mathrm{label}}(\mathrm{Nb}_{\sigma_{\mathrm{edge}}}(\sigma_{\mathrm{label}}^{-1}(l),\alpha))$. Its compressed version replaces the random permutations by **databases** that are recorded lazily: a **label database** $L:[M]\rightharpoonup[M]$ (a partial injection, with the convention $L(0)=0$, $0\notin\mathrm{Dom}(L)$) and an **edge database** $C=(C_b)_{b\in B_{\mathrm{edge}}}$ with partial injections $C_b:E_b\rightharpoonup E_b$ on each permuted edge class.
--
--   For a fixed edge database the **partial neighbor map** $\mathrm{Nb}_C(v,\alpha)$ follows the edge $e=e_\alpha(v)$: unpermuted edges are followed directly, a permuted edge is followed through $C_b$ (forward if $v=\mathrm{tail}(e)$, backward if $v=\mathrm{head}(e)$), and the value is $\bot$ when the needed record is absent; set $s_F(l,\alpha,L,C)=\mathrm{Nb}_C(L^{-1}(l),\alpha)$ if $l\in\mathrm{Im}(L)\cup\{0\}$ and $\bot$ otherwise. From the compression primitive $\mathrm{pCF}(|\psi_1\rangle,|\psi_2\rangle)$ one builds
--
--   1. $\mathrm{pC}^{\mathrm{inv}}_{\mathrm{lab}}$: on $l\in[M]$, $\bigoplus_{L:\,l\notin\mathrm{Im}(L)}\mathrm{pCF}(|+^{\mathrm{inv}}_{l,L}\rangle,|L\rangle)$ with $|+^{\mathrm{inv}}_{l,L}\rangle=(M-|L|)^{-1/2}\sum_{v\notin\mathrm{Dom}(L)}|L[v\to l]\rangle$;
--   2. $\mathrm{pC}_{\mathrm{edge}}$: if $l\in\mathrm{Im}(L)$ and $v=L^{-1}(l)$, apply to $C_b$ the forward compression $\mathrm{pC}^{\to}_{e,b}$ (if $v=\mathrm{tail}(e)$) or the backward compression $\mathrm{pC}^{\leftarrow}_{e,b}$ (if $v=\mathrm{head}(e)$), $e=e_\alpha(v)$;
--   3. $\mathrm{pC}^{\mathrm{for}}_{\mathrm{lab}}$: if $w=s_F(l,\alpha,L,C)\notin\{\bot,L^{-1}(l),0\}$, apply $\bigoplus_{L:\,w\notin\mathrm{Dom}(L)}\mathrm{pC}_{w,L}$ to $L$;
--   4. $P$: XOR $L(w)$ into $Y$ when $w=s_F(l,\alpha,L,C)\in\mathrm{Dom}(L)\cup\{0\}$.
--
--   The **ordinary compressed welded trees oracle** is
--   $$
--   \mathrm{cpWT}=\mathrm{pC}^{\mathrm{inv}}_{\mathrm{lab}}\cdot\mathrm{pC}_{\mathrm{edge}}\cdot\mathrm{pC}^{\mathrm{for}}_{\mathrm{lab}}\cdot P\cdot(\mathrm{pC}^{\mathrm{for}}_{\mathrm{lab}})^\dagger\cdot(\mathrm{pC}_{\mathrm{edge}})^\dagger\cdot(\mathrm{pC}^{\mathrm{inv}}_{\mathrm{lab}})^\dagger .
--   $$
--   It is the operator whose action on good database states is analysed in §4 (Theorem 4.9).
--
--   **Formalization Note** Each operator is the linear extension of the action on basis states displayed in (30)–(39). $[M]$ is `Fin M` (index $i$ for the number $i+1$); each $C_b$ is an injective database over a fixed enumeration of $E_b$; the forward compressions are the published `pC`, the backward ones (30), (34) are `pCinv`. Queried labels $l>M$ are fixed by every factor.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §3.2, (29)–(40) and Definition 3.4, pp.18–19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_WeldedPath_oracleFn
import Definitions.Def_WeldedPath_cpO

namespace WeldedPath

namespace Supplement

open QAlgorithms WeldedInstance InjDb

variable {n : ℕ}

/-! ### Registers -/

/-- The permuted edge classes `b ∈ B_edge`, as a type (Carolan, Childs, Coudron, Gilani,
Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard,
arXiv:2611.05912 (sha256 b31400a0…), §3.1, p.16). -/
abbrev PClass (n l : ℕ) := ↥(BEdge n l)

/-- `|E_b|`, the number of edges of the permuted class `b` (arXiv:2611.05912 (sha256 b31400a0…),
p.16). -/
def classSize (l : ℕ) (G : WeldedInstance n) (b : PClass n l) : ℕ := (G.classEdges l b.1).card

/-- The fixed enumeration `E_b ≃ [|E_b|]` of the edges of a permuted class, under which an edge
database `C_b : E_b ⇀ E_b` is an injective database `I_{|E_b|}`.

**Formalization Note.** Any fixed enumeration gives the same operators up to this relabeling of
the register `C_b`; the statements of this mission do not depend on the choice. -/
noncomputable def edgeIdx (l : ℕ) (G : WeldedInstance n) (b : PClass n l) :
    ↥(G.classEdges l b.1) ≃ Fin (classSize l G b) :=
  (G.classEdges l b.1).equivFin

/-- The label database register: partial injections `L : [M] ⇀ [M]` (arXiv:2611.05912
(sha256 b31400a0…), §3.2, p.18).

**Formalization Note.** `[M] = {1, …, M}` is `Fin M`, the index `i` standing for the number
`i + 1`, both for the structural vertex in the domain and for the label in the image. The entrance
convention `L(0) = 0` is not a record (`0 ∉ Dom(L)`); it is applied by `lookupL` and `invL`. -/
abbrev LabelDb (n : ℕ) := InjDb (labelBound n)

/-- The edge database register `C = (C_b)_{b ∈ B_edge}`, `C_b : E_b ⇀ E_b` (arXiv:2611.05912
(sha256 b31400a0…), p.18), each `C_b` an injective database over the enumeration `edgeIdx`. -/
abbrev EdgeDb (l : ℕ) (G : WeldedInstance n) := (b : PClass n l) → InjDb (classSize l G b)

/-- The database register `I = (L, C)` (arXiv:2611.05912 (sha256 b31400a0…), p.18). -/
abbrev Db (l : ℕ) (G : WeldedInstance n) := LabelDb n × EdgeDb l G

/-- Decidable equality of database basis states. -/
instance instDecEqDb (l : ℕ) (G : WeldedInstance n) : DecidableEq (Db l G) := inferInstance

/-- The query registers `|l, α⟩_X |a⟩_Y` of the welded trees oracle, `l` and `a` strings of
`2n + 1` bits (arXiv:2611.05912 (sha256 b31400a0…), pp.17–18); the same type as the query
register of `QAlgorithms.QueryAlg` used by the published `successProb`. -/
abbrev QReg (n : ℕ) := (Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)

/-- The empty database `|⊥⟩_I`: no label and no edge records (arXiv:2611.05912
(sha256 b31400a0…), Definition 3.4, p.19). -/
def emptyDb (l : ℕ) (G : WeldedInstance n) : Db l G := (⊥, fun _ => ⊥)

/-- The number of records `|I| = |L| + |C|`, `|C| = Σ_b |C_b|` (arXiv:2611.05912
(sha256 b31400a0…), p.18). -/
def dbSize {l : ℕ} {G : WeldedInstance n} (I : Db l G) : ℕ :=
  I.1.size + ∑ b, (I.2 b).size

/-! ### Reading the databases -/

/-- The element of `[M]` (an index of `Fin M`) named by the number `x`, if `1 ≤ x ≤ M`. -/
def toIdx (n x : ℕ) : Option (Fin (labelBound n)) :=
  if h : 1 ≤ x ∧ x ≤ labelBound n then some ⟨x - 1, by omega⟩ else none

/-- `L(w)` with the convention `L(0) = 0` (arXiv:2611.05912 (sha256 b31400a0…), p.18): `some 0`
for `w = 0`, `some (L(w))` for `w ∈ Dom(L)`, `none` otherwise. -/
def lookupL (L : LabelDb n) (w : ℕ) : Option ℕ :=
  if w = 0 then some 0 else (toIdx n w).bind fun i => (L i).map fun j => j.1 + 1

/-- `L^{-1}(l)` with the convention `L^{-1}(0) = 0` (arXiv:2611.05912 (sha256 b31400a0…), p.18,
(37)): `some 0` for `l = 0`, `some (L^{-1}(l))` for `l ∈ Im(L)`, `none` otherwise. -/
def invL (L : LabelDb n) (x : ℕ) : Option ℕ :=
  if x = 0 then some 0 else (toIdx n x).bind fun j => (L.symm j).map fun i => i.1 + 1

/-- The permuted-class data of `e_α(v)`: the class `b = b_edge(e) ∈ B_edge`, the edge `e ∈ E_b`, and
whether `v = tail(e)` (`true`) or `v = head(e)` (`false`). `none` if `v ∉ V_n`, `e_α(v) = ⊥`, or
`b_edge(e) = ⊥` (arXiv:2611.05912 (sha256 b31400a0…), (29), (35)). -/
noncomputable def permData (l : ℕ) (G : WeldedInstance n) (v : ℕ) (α : Fin 3) :
    Option ((b : PClass n l) × ↥(G.classEdges l b.1) × Bool) :=
  open Classical in
  if ¬ IsVertex n v then none
  else
    match G.eAlpha v α with
    | none => none
    | some e =>
      if h : e ∈ G.edges ∧ ∃ b ∈ BEdge n l, G.bEdge l e = some b ∧ (v = e.tail ∨ v = e.head n) then
        let b : PClass n l := ⟨Classical.choose h.2, (Classical.choose_spec h.2).1⟩
        some ⟨b, ⟨e, Finset.mem_filter.2 ⟨h.1, (Classical.choose_spec h.2).2.1⟩⟩,
          decide (v = e.tail)⟩
      else none

/-- The partial neighbor map `Nb_C(v, α)` (29) (arXiv:2611.05912 (sha256 b31400a0…), p.18), for
`e = e_α(v)`, `b = b_edge(e)`: `v` if `v ∉ V_n` or `e = ⊥`; `head(e)` / `tail(e)` if `b = ⊥` and
`v = tail(e)` / `v = head(e)`; `head(C_b(e))` if `b ∈ B_edge`, `v = tail(e)`, `e ∈ Dom(C_b)`;
`tail(C_b^{-1}(e))` if `b ∈ B_edge`, `v = head(e)`, `e ∈ Im(C_b)`; `⊥` (`none`) otherwise.

**Formalization Note.** The fallback `some v` for an edge `e_α(v)` that is not incident to `v` or
not an edge of the instance never occurs (the same fallback as the published `Nb`). -/
noncomputable def NbC (l : ℕ) (G : WeldedInstance n) (C : EdgeDb l G) (v : ℕ) (α : Fin 3) :
    Option ℕ :=
  if ¬ IsVertex n v then some v
  else
    match G.eAlpha v α with
    | none => some v
    | some e =>
      match permData l G v α with
      | some ⟨b, e', isTail⟩ =>
        if isTail then (C b (edgeIdx l G b e')).map fun j => ((edgeIdx l G b).symm j).1.head n
        else ((C b).symm (edgeIdx l G b e')).map fun j => ((edgeIdx l G b).symm j).1.tail
      | none =>
        if G.bEdge l e = none then
          (if v = e.tail then some (e.head n) else if v = e.head n then some e.tail else some v)
        else some v

/-- The partial map `sF(l, α, L, C)` (37) (arXiv:2611.05912 (sha256 b31400a0…), p.19):
`Nb_C(L^{-1}(l), α)` if `l ∈ Im(L) ∪ {0}` (with `L^{-1}(0) = 0`), `⊥` otherwise. -/
noncomputable def sF (l : ℕ) (G : WeldedInstance n) (x : ℕ) (α : Fin 3) (L : LabelDb n)
    (C : EdgeDb l G) : Option ℕ :=
  (invL L x).bind fun v => NbC l G C v α

/-! ### Operators from basis images -/

/-- The linear operator with prescribed images `|p⟩ ↦ f(p)` of the basis states. -/
noncomputable def ofBasis {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (f : X → Hil Y) : Hil X →L[ℂ] Hil Y :=
  ∑ p : X, ketBra (f p) (ket p)

/-- The image `Σ_{a'} ⟨a'|T|a⟩ |set a'⟩` of a basis state under an operator `T` acting on one
part `a` of it (identity on the rest; `set` puts a new value of that part back). -/
noncomputable def partImg {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    (T : Hil A →L[ℂ] Hil A) (a : A) (set : A → X) : Hil X :=
  ∑ a' : A, inner ℂ (ket a') (T (ket a)) • ket (set a')

/-! ### The compression operators (30)–(39) -/

/-- `|+^{inv}_{x,I}⟩ = (s − |I|)^{-1/2} Σ_{v ∈ [s] ∖ Dom(I)} |I[v → x]⟩` for `x ∉ Im(I)`
((30) and (33), arXiv:2611.05912 (sha256 b31400a0…), p.18). -/
noncomputable def plusInv {s : ℕ} (I : InjDb s) (x : Fin s) : Hil (InjDb s) :=
  ((Real.sqrt ((s - I.size : ℕ) : ℝ))⁻¹ : ℂ) •
    ∑ v ∈ Finset.univ.filter (fun v => I v = none), ket (I.addPair v x)

/-- The inverse compression operator `⨁_{I : x ∉ Im(I)} pCF(|+^{inv}_{x,I}⟩, |I⟩)`: `pC^{inv}_l`
of (30) on the label database (`s = M`) and `pC^←_{e,b}` of (34) on `C_b` (`s = |E_b|`)
(arXiv:2611.05912 (sha256 b31400a0…), p.18).

**Formalization Note.** As for the published `pC`, the direct sum is
`1 + Σ_I (pCF(|+^{inv}_{x,I}⟩, |I⟩) − 1)`, each summand supported on `span{|I⟩, |I[v → x]⟩}`. -/
noncomputable def pCinv (s : ℕ) (x : Fin s) : Hil (InjDb s) →L[ℂ] Hil (InjDb s) :=
  1 + ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I.symm x = none),
    (pCF (plusInv I x) (ket I) - 1)

/-- The inverse-label compression operator `pC^{inv}_lab` (30) (arXiv:2611.05912
(sha256 b31400a0…), p.18): `|l, α⟩_X (pC^{inv}_l |L⟩_L)` if `l ∈ [M]`, the identity if
`l ∉ [M]`; identity on `Y` and `C`. The queried label `l` is the number encoded by the
`(2n+1)`-bit string of `X` (most significant bit first, as for the published `oracleFn`). -/
noncomputable def pCinvLab (l : ℕ) (G : WeldedInstance n) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G) :=
  ofBasis fun p =>
    match toIdx n (bitsToNat p.1.1.1) with
    | some x => partImg (pCinv (labelBound n) x) p.2.1 fun L' => (p.1, (L', p.2.2))
    | none => ket p

/-- `pC'_{v,α}` (35) on the edge database (arXiv:2611.05912 (sha256 b31400a0…), p.19), for
`e = e_α(v)`, `b = b_edge(e)`: `pC^→_{e,b}` (32) (the published `pC` on `C_b`) if `b ∈ B_edge` and
`v = tail(e)`; `pC^←_{e,b}` (34) (`pCinv` on `C_b`) if `b ∈ B_edge` and `v = head(e)`; `1`
otherwise. Here it is given by the image of a basis state `|C⟩` of the edge register. -/
noncomputable def pCprimeImg (l : ℕ) (G : WeldedInstance n) (v : ℕ) (α : Fin 3)
    {X : Type*} [Fintype X] [DecidableEq X] (C : EdgeDb l G) (set : EdgeDb l G → X) : Hil X :=
  match permData l G v α with
  | some ⟨b, e, isTail⟩ =>
    partImg (if isTail then pC (classSize l G b) (edgeIdx l G b e)
        else pCinv (classSize l G b) (edgeIdx l G b e))
      (C b) fun D => set (Function.update C b D)
  | none => ket (set C)

/-- The controlled edge-compression operator `pC_edge` (36) (arXiv:2611.05912
(sha256 b31400a0…), p.19): `|l, α⟩_X |L⟩_L (pC'_{v,α} |C⟩_C)` if `l ∈ Im(L)` and `v = L^{-1}(l)`,
the identity otherwise.

**Formalization Note.** `l ∈ Im(L)` excludes `l = 0` (the source writes `Im(L) ∪ {0}` when `0` is
meant, (37)); at `l = 0` the edge of the entrance is not permuted, so `pC'_{0,α} = 1` anyway. -/
noncomputable def pCedge (l : ℕ) (G : WeldedInstance n) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G) :=
  ofBasis fun p =>
    let x := bitsToNat p.1.1.1
    if x = 0 then ket p
    else
      match invL p.2.1 x with
      | some v => pCprimeImg l G v p.1.1.2 p.2.2 fun C' => (p.1, (p.2.1, C'))
      | none => ket p

/-- The forward-label compression operator `pC^{for}_lab` (38)–(39) (arXiv:2611.05912
(sha256 b31400a0…), p.19): with `w = sF(l, α, L, C)`, `|l, α⟩_X (pC^{for}_w |L⟩_L) |C⟩_C` if
`w ∉ {⊥, L^{-1}(l), 0}`, the identity if `w ∈ {⊥, L^{-1}(l), 0}`. `pC^{for}_w =
⨁_{L : w ∉ Dom(L)} pC_{w,L}` is the published `pC` (6) on the label database at `w ∈ [M]`.

**Formalization Note.** `w` is a structural index of `G_n`, so `w ∈ [M]` whenever
`w ∉ {⊥, 0}`; the guard `toIdx` only fixes the value on numbers that never occur. -/
noncomputable def pCforLab (l : ℕ) (G : WeldedInstance n) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G) :=
  ofBasis fun p =>
    let x := bitsToNat p.1.1.1
    match sF l G x p.1.1.2 p.2.1 p.2.2 with
    | none => ket p
    | some w =>
      if some w = invL p.2.1 x ∨ w = 0 then ket p
      else
        match toIdx n w with
        | some i => partImg (pC (labelBound n) i) p.2.1 fun L' => (p.1, (L', p.2.2))
        | none => ket p

/-- The XOR operator `P` (arXiv:2611.05912 (sha256 b31400a0…), p.19):
`|l, α⟩_X |a ⊕ L(w)⟩_Y |L, C⟩_I` if `w = sF(l, α, L, C) ∈ Dom(L) ∪ {0}` (with `L(0) = 0`), the
identity otherwise. `L(w)` is written as its `(2n+1)`-bit string and `⊕` is bitwise XOR. -/
noncomputable def xorP (l : ℕ) (G : WeldedInstance n) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G) :=
  ofBasis fun p =>
    match (sF l G (bitsToNat p.1.1.1) p.1.1.2 p.2.1 p.2.2).bind (lookupL p.2.1) with
    | some y => ket ((p.1.1, p.1.2 + natToBits (2 * n + 1) y), p.2)
    | none => ket p

/-- The ordinary compressed welded trees oracle (Definition 3.4, (40); arXiv:2611.05912
(sha256 b31400a0…), p.19):
`cpWT := pC^{inv}_lab · pC_edge · pC^{for}_lab · P · (pC^{for}_lab)† · (pC_edge)† · (pC^{inv}_lab)†`,
an operator on `X ⊗ Y ⊗ L ⊗ C`.

**Formalization Note.**
1. Registers: `X` = `(2n+1)`-bit label string × color `Fin 3`, `Y` = `(2n+1)`-bit string,
   `L` = `LabelDb n`, `C` = `EdgeDb l G` (one injective database per permuted class, over a fixed
   enumeration of `E_b`). The algorithm's workspace is not touched.
2. Each operator is defined by its images of basis states, as in (30)–(39); queried labels
   `l > M` are fixed by every factor (p.17: "For `l > M`, all welded trees oracles act as the
   identity").
3. `†` is the Hilbert-space adjoint. -/
noncomputable def cpWT (l : ℕ) (G : WeldedInstance n) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G) :=
  (pCinvLab l G).comp ((pCedge l G).comp ((pCforLab l G).comp ((xorP l G).comp
    ((ContinuousLinearMap.adjoint (pCforLab l G)).comp
      ((ContinuousLinearMap.adjoint (pCedge l G)).comp
        (ContinuousLinearMap.adjoint (pCinvLab l G)))))))

end Supplement

end WeldedPath


