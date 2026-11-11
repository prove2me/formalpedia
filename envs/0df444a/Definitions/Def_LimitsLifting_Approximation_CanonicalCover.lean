-- Prove2me | Definitions.Def_LimitsLifting_Approximation_CanonicalCover
-- name    : LimitsLifting_Approximation_CanonicalCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:39.566668+00:00
-- url     : https://prove2.me/theorems/f4959766-53c2-41b7-bb49-03acd7c8d525
-- title:
--   Definitions 2.3, 3.1 — the canonical rectangle cover of $\mathrm{Search}(F)\circ\mathrm{Ind}_m^n$ and $f=f_{\mathcal R}$
-- statement:
--   Let $F$ be a CNF over the variables $[n]$ (a finite set of clauses, each a finite set of literals). The **index gadget** $\mathrm{Ind}_m:[m]\times\{0,1\}^m\to\{0,1\}$ maps $(a,b)\mapsto b[a]$, and $G=\mathrm{Ind}_m^n:[m]^n\times\{0,1\}^{mn}\to\{0,1\}^n$ maps $(x,y)\mapsto(y_1[x_1],\dots,y_n[x_n])$.
--
--   The **canonical rectangle cover** $\mathcal R=\mathcal R_{F,\mathrm{Ind}_m}$ has one rectangle for each clause $C\in F$ and each $\alpha\in[m]^{\mathrm{vars}(C)}$:
--   $$R_{C,\alpha}=\{x\in[m]^n: x_{\mathrm{vars}(C)}=\alpha\}\times\{y\in\{0,1\}^{mn}: \mathrm{Ind}_m^{\mathrm{vars}(C)}(\alpha,y_{\mathrm{vars}(C)})\text{ falsifies }C\}.$$
--   **Razborov's reduction** turns $\mathcal R$ into vectors indexed by the pairs $(C,\alpha)$: $A(x)_{C,\alpha}=1$ iff $x_{\mathrm{vars}(C)}=\alpha$, and $B(y)_{C,\alpha}=0$ iff $y$ lies in the second factor of $R_{C,\alpha}$. The partial monotone function $f=f_{\mathcal R}$ has domain $\mathcal Z_{m,n}=A([m]^n)\cup B(\{0,1\}^{mn})$, value $1$ on $A([m]^n)$ and $0$ on $B(\{0,1\}^{mn})$. It is not extended to the rest of the cube.
--
--   For $g\in\mathcal F(\mathcal Z_{m,n})$ the associated rectangle is $R_g=S_g\times T_g$ with $S_g=\{x: g(A(x))=1\}$ and $T_g=\{y: g(B(y))=0\}$. The **density** of $X\subseteq[m]^n$ is $|X|/m^n$ and of $Y\subseteq\{0,1\}^{mn}$ is $|Y|/2^{mn}$.
--
--   The **standing assumptions** of §4.3 on $F$: it is unsatisfiable (of arbitrary width $k$), every variable occurs in some clause, and no clause contains a literal together with its negation. $w_{\mathrm{Res}}(F)$ is the minimum width of a Resolution refutation of $F$.
--
--   These objects are the lifted function whose monotone complexity the mission bounds, and the bridge between rectangles and functions used by the approximation model $\mathcal M_w$.
--
--   **Formalization Note** $[m]=\{0,\dots,m-1\}$ (`Fin m`) and the variables are `Fin n`; Bob's input is $n$ blocks of $m$ bits. Literals, clauses, satisfaction, resolution refutations and their width are those of the published definition `MultiplierAssoc206_Resolution_CNF` (a literal $(i,b)$ asserts $z_i=b$); $w_{\mathrm{Res}}$ is its `refWidth`, an infimum in $\mathbb N$, attained for unsatisfiable $F$. For unsatisfiable $F$ the sets $A([m]^n)$ and $B(\{0,1\}^{mn})$ are disjoint, so $f$ is well defined.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Definition 2.3 (printed p. 12, PDF p. 13), Definition 3.1 (printed pp. 13–14, PDF pp. 14–15), §2.5 (printed p. 12, PDF p. 13), §4.2 and §4.3 (printed pp. 20–21, PDF pp. 21–22)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

noncomputable section

namespace LimitsLifting.Approximation

open Classical
open MultiplierAssoc206.Resolution

/-! # The canonical rectangle cover of `Search(F) ∘ Ind_m^n` and Razborov's reduction

Carenini, Cavalar, Grosser, Pich, *Limits of Lifting*, STOC 2027 submission #309,
Definition 2.3 (printed p. 12, PDF p. 13), Definition 3.1 (printed pp. 13–14, PDF pp. 14–15),
§2.5 (index gadget) and §4.2–4.3 (printed pp. 20–21, PDF pp. 21–22).

The CNF `F` is over the variables `Fin n` (the source's `[n]`), with clauses and literals as in
the published definition `MultiplierAssoc206_Resolution_CNF`: a literal `(i, b)` asserts `z i = b`.
The gadget `Ind_m : [m] × {0,1}^m → {0,1}` maps `(a, b) ↦ b[a]`; `[m]` is `Fin m`.
Alice's inputs are `x ∈ [m]^n` and Bob's are `y ∈ ({0,1}^m)^n = {0,1}^{mn}`. -/

/-- Alice's input space `[m]^n`. -/
abbrev AliceIn (n m : ℕ) := Fin n → Fin m

/-- Bob's input space `{0,1}^{mn}`, as `n` blocks of `m` bits. -/
abbrev BobIn (n m : ℕ) := Fin n → Fin m → Bool

/-- The `n`-fold index gadget `G = Ind_m^n : (x, y) ↦ (y_1[x_1], …, y_n[x_n])`. -/
def gadget {n m : ℕ} (x : AliceIn n m) (y : BobIn n m) : Fin n → Bool := fun i => y i (x i)

/-- The variables `vars(C)` of a clause. -/
def clauseVars {n : ℕ} (C : Clause (Fin n)) : Finset (Fin n) := C.image Prod.fst

/-- The coordinates `(C, α)` of the canonical rectangle cover `R_{F,Ind_m}`: a clause `C ∈ F` and
an assignment `α ∈ [m]^{vars(C)}`. -/
abbrev Coord {n : ℕ} (m : ℕ) (F : CNF (Fin n)) :=
  Σ C : {C : Clause (Fin n) // C ∈ F}, ({i : Fin n // i ∈ clauseVars C.1} → Fin m)

/-- The assignment `Ind_m^{vars(C)}(α, y_{vars(C)})` to the variables of `C`, extended by `false`
outside `vars(C)` (those values are never read when evaluating `C`). -/
def gadgetOnClause {n m : ℕ} (C : Clause (Fin n)) (α : {i : Fin n // i ∈ clauseVars C} → Fin m)
    (y : BobIn n m) : Fin n → Bool :=
  fun i => if h : i ∈ clauseVars C then y i (α ⟨i, h⟩) else false

/-- The canonical rectangle `R_{C,α} = {x : x_{vars(C)} = α} × {y : Ind^{vars(C)}(α, y_{vars(C)})
falsifies C}` (Definition 3.1), as a pair of finite sets. -/
def canonRect {n m : ℕ} {F : CNF (Fin n)} (c : Coord m F) :
    Finset (AliceIn n m) × Finset (BobIn n m) :=
  (Finset.univ.filter (fun x => ∀ i : {i : Fin n // i ∈ clauseVars c.1.1}, x i.1 = c.2 i),
   Finset.univ.filter (fun y => ¬ ClauseSat (gadgetOnClause c.1.1 c.2 y) c.1.1))

/-- Razborov's map `A`: `A(x)_{C,α} = 1` iff `x ∈ {x : x_{vars(C)} = α}`. -/
def encA {n m : ℕ} (F : CNF (Fin n)) (x : AliceIn n m) : Coord m F → Bool :=
  fun c => decide (x ∈ (canonRect c).1)

/-- Razborov's map `B`: `B(y)_{C,α} = 0` iff `y ∈ {y : Ind^{vars(C)}(α, y) falsifies C}`. -/
def encB {n m : ℕ} (F : CNF (Fin n)) (y : BobIn n m) : Coord m F → Bool :=
  fun c => !decide (y ∈ (canonRect c).2)

/-- The domain `Z_{m,n} = A([m]^n) ∪ B({0,1}^{mn})` of `f = f_R`. -/
def liftDomain {n : ℕ} (m : ℕ) (F : CNF (Fin n)) : Set (Coord m F → Bool) :=
  Set.range (encA (m := m) F) ∪ Set.range (encB (m := m) F)

/-- The partial monotone function `f = f_{R_{F,Ind_m}}` of Razborov's reduction (Definition 2.3)
on its domain `Z_{m,n}`: value `1` on `A([m]^n)` and `0` on `B({0,1}^{mn})`. (For unsatisfiable
`F` the two sets are disjoint.) -/
noncomputable def liftedFn {n : ℕ} (m : ℕ) (F : CNF (Fin n)) : liftDomain m F → Bool :=
  fun z => decide (z.1 ∈ Set.range (encA (m := m) F))

/-- The rectangle `R_g = S_g × T_g` of a function `g ∈ F(Z_{m,n})`:
`S_g = {x : g(A(x)) = 1}` and `T_g = {y : g(B(y)) = 0}` (§4.3). -/
def rectOf {n m : ℕ} {F : CNF (Fin n)} (g : liftDomain m F → Bool) :
    Finset (AliceIn n m) × Finset (BobIn n m) :=
  (Finset.univ.filter (fun x => g ⟨encA F x, Or.inl ⟨x, rfl⟩⟩ = true),
   Finset.univ.filter (fun y => g ⟨encB F y, Or.inr ⟨y, rfl⟩⟩ = false))

/-- The input coordinate `x_{(C,α)}` as a partial function on `Z_{m,n}`. -/
def inputFn {n m : ℕ} {F : CNF (Fin n)} (c : Coord m F) : liftDomain m F → Bool :=
  fun z => z.1 c

/-- The density `|X| / m^n` of a set of Alice inputs. -/
noncomputable def aliceDensity {n m : ℕ} (X : Finset (AliceIn n m)) : ℝ :=
  (X.card : ℝ) / (m : ℝ) ^ n

/-- The density `|Y| / 2^{mn}` of a set of Bob inputs. -/
noncomputable def bobDensity {n m : ℕ} (Y : Finset (BobIn n m)) : ℝ :=
  (Y.card : ℝ) / (2 : ℝ) ^ (m * n)

/-- The standing assumptions of §4.3 (printed p. 21): `F` is an unsatisfiable CNF over `[n]`
(of any width `k`), every variable occurs in some clause, and no clause contains both a literal
and its negation. -/
def StandingCNF {n : ℕ} (F : CNF (Fin n)) : Prop :=
  Unsatisfiable F ∧ (∀ i : Fin n, i ∈ cnfVars F) ∧ ∀ C ∈ F, ¬ IsTautology C

/-- `w_Res(F)`: the minimum width of a resolution refutation of `F`, from the published
definition (`refWidth`). -/
noncomputable def wRes {n : ℕ} (F : CNF (Fin n)) : ℕ := refWidth F

end LimitsLifting.Approximation

end


