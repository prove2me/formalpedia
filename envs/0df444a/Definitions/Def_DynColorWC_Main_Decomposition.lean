-- Prove2me | Definitions.Def_DynColorWC_Main_Decomposition
-- name    : DynColorWC_Main_Decomposition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:47:32.328463+00:00
-- url     : https://prove2.me/theorems/247e0705-b744-4ef8-acb9-2ab14523ab0b
-- title:
--   The smooth dynamic ε-almost-clique decomposition (Definition 4.1) as written by the machine, its recourse (Definition 4.3), and the inlier labels
-- statement:
--   The data structure of Definition 4.1 keeps a map $C:V\to\mathbb N\cup\{\perp\}$, sets $\tilde A(v),\tilde E(v)\subseteq V$, labels $\ell:\mathbb N\to\{\mathrm{Reg},\mathrm{Irr}\}$, reals $z:\mathbb N\to\mathbb R$, and sets $B\subseteq V$, $I_B\subseteq\mathbb N$; Theorem 3 adds labels $\ell':V\to\{\mathrm{In},\mathrm{Out}\}$. $C_i=\{v:C(v)=i\}$ and $V_{sp}=\{v:C(v)=\perp\}$; $C(v)$ also denotes the cluster of $v$ ($\emptyset$ if $C(v)=\perp$), $A(v)=C(v)\setminus N[v]$ and $E(v)=N(v)\setminus C(v)$; $\mathrm{inliers}(C_i)=\{v\in C_i:\ell'(v)=\mathrm{In}\}$, $\mathrm{outliers}(C_i)=\{v\in C_i:\ell'(v)=\mathrm{Out}\}$.
--
--   It is a **smooth $\varepsilon$-almost-clique decomposition** of $G$ (with sparsity constant $c$) if
--   1. every $v$ with $C(v)=\perp$ or $\ell(C(v))\ne\mathrm{Reg}$ is $c\,\varepsilon^2\Delta$-sparse;
--   2. each regular $C_i$ is an $\varepsilon$-almost-clique and, if nonempty, $z(C_i)=z(i)$;
--   3. $B\subseteq V_{sp}$, $|I_B|\le|B|\le2$, and every $v\notin B$ satisfies: (a) if $C(v)\notin I_B$ then $A(v)=\tilde A(v)$ and $E(v)=\tilde E(v)$; (b) if $C(v)\in I_B$ then $A(v)\setminus B\subseteq\tilde A(v)\subseteq A(v)\cup B$ and $E(v)\setminus B\subseteq\tilde E(v)\subseteq E(v)\cup B$.
--
--   **Recourse** (Definition 4.3): for a set-valued quantity $S_t$, $\sum_{t=\tau'}^{\tau}|S_t\oplus S_{t-1}|$; for the partition, $\sum_{t=\tau'}^{\tau}|\{v:C_t(v)\ne C_{t-1}(v)\}|$.
--
--   **What the machine reports.** The structure is the program's own change log: output words are read in records $(\mathrm{tag},a,b,c)$ and applied in order to the initial structure (all $\perp$, all sets empty, all labels Irr/Out, all $z(i)=0$): tag 0 sets $C(a)$ ($\perp$ if $b=0$, else $b-1$); tags 1, 2 toggle $b$ in $\tilde A(a)$, $\tilde E(a)$; tag 3 sets $\ell(a)=\mathrm{Reg}$ iff $b=1$; tag 4 sets $z(a)=b/c$; tags 5, 6 toggle $a$ in $B$, $I_B$; tag 7 sets $\ell'(a)=\mathrm{In}$ iff $b=1$.
--
--   **Formalization Note.** "$\Omega(\varepsilon^2\Delta)$-sparse" is $c\,\varepsilon^2\Delta$-sparse with the constant $c$ as a parameter; theorems quantify it as an absolute constant. The inverse map $i\mapsto C_i$ that the paper also requires is read off $C$. $z(i)$ is reported as a rational, which suffices since $z(C_i)$ is rational.
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Definition 4.1, p. 16 (PDF 18); Definition 4.3, p. 17 (PDF 19); Theorem 3, p. 18 (PDF 20)

import Mathlib
import Definitions.Def_DynColorWC_Main_Model
import Definitions.Def_DynColorWC_Main_AlmostClique

namespace DynColorWC.Main

/-! # The smooth dynamic ε-almost-clique decomposition, as reported by the machine

Flin and Ghaffari (2026), *Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time*,
STOC 2027 submission, supplied PDF sha256 93ebb2ff…3154300e3: Definition 4.1, p. 16 (PDF 18);
Definition 4.3, p. 17 (PDF 19); the labels `ℓ′` and the sets `inliers(C)`, `outliers(C)` of
Theorem 3, p. 18 (PDF 20).

**The data structure** (Definition 4.1) keeps `C : V → ℕ ∪ {⊥}` (`none` is `⊥`), the sets
`Ã(v), Ẽ(v)`, labels `ℓ : ℕ → {Reg, Irr}` (`true` is `Reg`), reals `z : ℕ → ℝ`, sets `B ⊆ V` and
`I_B ⊆ ℕ`; Theorem 3 adds the labels `ℓ′ : V → {In, Out}` (`true` is `In`).

**What the machine reports.** As for the coloring, the structure is what the machine itself writes:
its output words are read in records of four words `tag, a, b, c`, applied in order to the
initial structure (every `C(v) = ⊥`, every `Ã(v) = Ẽ(v) = ∅`, every `ℓ(i) = Irr`, every `z(i) = 0`,
`B = I_B = ∅`, every `ℓ′(v) = Out`):

| tag | effect |
|---|---|
| 0 | `C(a) := ⊥` if `b = 0`, else `C(a) := b − 1` |
| 1 | toggle the membership of `b` in `Ã(a)` |
| 2 | toggle the membership of `b` in `Ẽ(a)` |
| 3 | `ℓ(a) := Reg` if `b = 1`, else `Irr` |
| 4 | `z(a) := b / c` (a rational value; `c = 0` gives `0`) |
| 5 | toggle the membership of `a` in `B` |
| 6 | toggle the membership of `a` in `I_B` |
| 7 | `ℓ′(a) := In` if `b = 1`, else `Out` |

A record naming a vertex `≥ n`, or with an unknown tag, changes nothing; trailing words that do not
form a record are ignored. The inverse map `i ↦ C_i` of Definition 4.1 is determined by `C`
(`clusterSet`). -/

/-- The data structure of Definition 4.1 together with the labels `ℓ′` of Theorem 3. -/
structure DecompState (n : ℕ) where
  C : Fin n → Option ℕ
  At : Fin n → Finset (Fin n)
  Et : Fin n → Finset (Fin n)
  reg : ℕ → Bool
  z : ℕ → ℝ
  B : Finset (Fin n)
  IB : Finset ℕ
  inl : Fin n → Bool

/-- The initial structure: every vertex unclustered, all sets empty, every label `Irr`/`Out`,
every `z(i) = 0`. -/
def DecompState.init (n : ℕ) : DecompState n :=
  ⟨fun _ => none, fun _ => ∅, fun _ => ∅, fun _ => false, fun _ => 0, ∅, ∅, fun _ => false⟩

/-- Toggle the membership of `x` in `S`. -/
def toggle {α : Type} [DecidableEq α] (S : Finset α) (x : α) : Finset α :=
  if x ∈ S then S.erase x else insert x S

/-- Apply one record `tag, a, b, c` to the structure. -/
noncomputable def applyRecord {n : ℕ} (D : DecompState n) (tag a b c : ℕ) : DecompState n :=
  if ha : a < n then
    let v : Fin n := ⟨a, ha⟩
    match tag with
    | 0 => { D with C := Function.update D.C v (if b = 0 then none else some (b - 1)) }
    | 1 => if hb : b < n then
             { D with At := Function.update D.At v (toggle (D.At v) ⟨b, hb⟩) } else D
    | 2 => if hb : b < n then
             { D with Et := Function.update D.Et v (toggle (D.Et v) ⟨b, hb⟩) } else D
    | 3 => { D with reg := Function.update D.reg a (b = 1) }
    | 4 => { D with z := Function.update D.z a ((b : ℝ) / (c : ℝ)) }
    | 5 => { D with B := toggle D.B v }
    | 6 => { D with IB := toggle D.IB a }
    | 7 => { D with inl := Function.update D.inl v (b = 1) }
    | _ => D
  else
    match tag with
    | 3 => { D with reg := Function.update D.reg a (b = 1) }
    | 4 => { D with z := Function.update D.z a ((b : ℝ) / (c : ℝ)) }
    | 6 => { D with IB := toggle D.IB a }
    | _ => D

/-- Apply a list of output words, read as records of four words, in order. -/
noncomputable def applyRecords {n : ℕ} : DecompState n → List ℕ → DecompState n
  | D, tag :: a :: b :: c :: rest => applyRecords (applyRecord D tag a b c) rest
  | D, _ => D

/-- The structure reported after preprocessing on `inp` and the first `t` updates of `σ`. -/
noncomputable def decompAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : DecompState n :=
  applyRecords (DecompState.init n) (outputAt P ω inp σ t)

/-- The structure just before the completed state `t`: the initial structure for `t = 0`, and
the structure after update `t − 1` otherwise. -/
noncomputable def decompBefore (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : DecompState n :=
  if t = 0 then DecompState.init n else decompAt P ω inp σ (t - 1)

/-- The cluster `C_i = {v : C(v) = i}`. -/
def clusterSet {n : ℕ} (D : DecompState n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => D.C v = some i

/-- The cluster of `v` (`∅` when `C(v) = ⊥`). -/
def clusterOf {n : ℕ} (D : DecompState n) (v : Fin n) : Finset (Fin n) :=
  match D.C v with
  | some i => clusterSet D i
  | none => ∅

/-- `inliers(C_i) = {v ∈ C_i : ℓ′(v) = In}`. -/
def inliers {n : ℕ} (D : DecompState n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => D.C v = some i ∧ D.inl v = true

/-- `outliers(C_i) = {v ∈ C_i : ℓ′(v) = Out}`. -/
def outliers {n : ℕ} (D : DecompState n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => D.C v = some i ∧ D.inl v = false

/-- Definition 4.1: `D` is a smooth `ε`-almost-clique decomposition of `G` for the degree bound `Δ`,
with sparsity constant `cSp` for Part 1 ("`Ω(ε²Δ)`-sparse" means `cSp·ε²·Δ`-sparse).
`A(v) = C(v) \ N[v]` and `E(v) = N(v) \ C(v)` are taken with the cluster `C(v)` of `D`
(`∅` for unclustered `v`).
1. every `v` with `C(v) = ⊥` or `ℓ(C(v)) ≠ Reg` is `cSp ε² Δ`-sparse;
2. each regular `C_i` is an `ε`-almost-clique and, when nonempty, `z(C_i) = z(i)`;
3. `B ⊆ V_sp`, `|I_B| ≤ |B| ≤ 2`, and every `v ∉ B` satisfies (a) if `C(v) ∉ I_B` then
   `A(v) = Ã(v)` and `E(v) = Ẽ(v)`; (b) if `C(v) ∈ I_B` then `A(v) \ B ⊆ Ã(v) ⊆ A(v) ∪ B` and
   `E(v) \ B ⊆ Ẽ(v) ⊆ E(v) ∪ B`. -/
def IsSmoothACD {n : ℕ} (ε cSp : ℝ) (Δ : ℕ) (G : SimpleGraph (Fin n)) (D : DecompState n) :
    Prop :=
  (∀ v, (D.C v = none ∨ ∃ i, D.C v = some i ∧ D.reg i = false) →
      IsSparse Δ G v (cSp * ε ^ 2 * Δ)) ∧
  (∀ i, D.reg i = true →
      IsAlmostClique ε Δ G (clusterSet D i) ∧
      ((clusterSet D i).Nonempty → zC Δ G (clusterSet D i) = D.z i)) ∧
  ((∀ v ∈ D.B, D.C v = none) ∧ D.IB.card ≤ D.B.card ∧ D.B.card ≤ 2 ∧
    ∀ v, v ∉ D.B →
      ((∀ i, D.C v = some i → i ∉ D.IB) →
          antiNbhd G (clusterOf D v) v = D.At v ∧ extNbhd G (clusterOf D v) v = D.Et v) ∧
      (∀ i, D.C v = some i → i ∈ D.IB →
          antiNbhd G (clusterOf D v) v \ D.B ⊆ D.At v ∧
          D.At v ⊆ antiNbhd G (clusterOf D v) v ∪ D.B ∧
          extNbhd G (clusterOf D v) v \ D.B ⊆ D.Et v ∧
          D.Et v ⊆ extNbhd G (clusterOf D v) v ∪ D.B))

/-- Definition 4.3, for one set-valued quantity `S_t`: its recourse over updates `[τ', τ]` is
`Σ_{t=τ'}^{τ} |S_t ⊕ S_{t−1}|` (used with `τ' ≥ 1`). -/
def setRecourse {α : Type} [DecidableEq α] (S : ℕ → Finset α) (τ' τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc τ' τ, (symmDiff (S t) (S (t - 1))).card

/-- Definition 4.3: the recourse of the vertex partition over updates `[τ', τ]`:
`Σ_{t=τ'}^{τ} H(C_t, C_{t−1})`, where `H` counts the vertices whose `C`-value differs. -/
def partitionRecourse {n : ℕ} (D : ℕ → DecompState n) (τ' τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc τ' τ, (Finset.univ.filter fun v => (D t).C v ≠ (D (t - 1)).C v).card

/-- The cluster identifiers in use in `D` or `D'`. -/
def clusterIds {n : ℕ} (D D' : DecompState n) : Finset ℕ :=
  Finset.univ.biUnion fun v => ((D.C v).toFinset ∪ (D'.C v).toFinset)

end DynColorWC.Main


