-- Prove2me | Definitions.Def_LimitsLifting_Approximation_RectangleScheme
-- name    : LimitsLifting_Approximation_RectangleScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:05.346221+00:00
-- url     : https://prove2.me/theorems/6348d4fd-4760-4b5b-a774-0ea0f552a7d3
-- title:
--   Definitions 4.6, 4.9, Lemma 4.7 — structured rectangles, Rectangle Scheme interface, the model $\mathcal M_w$
-- statement:
--   A **restriction** $\rho\in\{0,1,*\}^n$ has fixed coordinates $\mathrm{fix}(\rho)$ and free ones $\mathrm{free}(\rho)$; its width is $|\mathrm{fix}(\rho)|$. A nonempty rectangle $X\times Y\subseteq[m]^n\times\{0,1\}^{mn}$ is **$\rho$-structured** (Definition 4.6) if
--   1. $X_{\mathrm{fix}(\rho)}$ is fixed and every $z\in G(X\times Y)$ is consistent with $\rho$;
--   2. for every nonempty $I\subseteq\mathrm{free}(\rho)$, the marginal of the uniform distribution $\mathbf X$ on $X$ satisfies $H_\infty(\mathbf X_I)\ge 0.9\,|I|\log m$;
--   3. $H_\infty(\mathbf Y)\ge mn-n^3$.
--
--   It is **$\rho$-like** if $G(X\times Y)$ equals the subcube of strings consistent with $\rho$.
--
--   A **Rectangle Scheme** with constant $K$ is any map that, given a parameter $0<w\le n$ and a rectangle $R$, outputs a partition of $R$ into structured pieces and error pieces together with error sets $X_{\mathrm{err}}\subseteq[m]^n$, $Y_{\mathrm{err}}\subseteq\{0,1\}^{mn}$ of density at most $n^{-w}$, such that each structured piece is $\rho_i$-structured with $|\mathrm{fix}(\rho_i)|\le Kw$, each error piece lies in $X_{\mathrm{err}}\times\{0,1\}^{mn}\cup[m]^n\times Y_{\mathrm{err}}$, and (query alignment) every $x\notin X_{\mathrm{err}}$ has a set $I_x\subseteq[n]$, $|I_x|\le Kw$, containing $\mathrm{fix}(\rho_i)$ for every structured piece meeting $\{x\}\times\{0,1\}^{mn}$. These are exactly the properties stated in Lemma 4.7.
--
--   Given such a scheme, the **approximating gate** $g\mathbin{\bar\circ}h$ ($\circ\in\{\wedge,\vee\}$, Definition 4.9) equals $g\circ h$ if $g$ or $h$ is a constant function; otherwise it agrees with $g\circ h$ except that it is $0$ on $A(X_{\mathrm{err}})$ and $1$ on $B(Y_{\mathrm{err}})$, where $X_{\mathrm{err}},Y_{\mathrm{err}}$ are the scheme's error sets on $R_{g\circ h}$. The model $\mathcal M_w$ is the set of all functions on $\mathcal Z_{m,n}$ computed by $\{\bar\vee,\bar\wedge\}$-circuits from the inputs $x_{(C,\alpha)}$ and $0,1$, with no bound on size; $\mu(f,\mathcal M_w)$ and $\varepsilon_{\mathcal M_w}(f)$ are as in Definition 4.3.
--
--   For a constant-free $\{\bar\vee,\bar\wedge\}$-circuit $B$, the **rectangle circuit** $\Pi_B$ attaches to a gate $g=h\mathbin{\bar\circ}h'$ the rectangle $R_g^*=R_{h\circ h'}$; the structured subrectangles of a gate node are the scheme's structured pieces on $R_g^*$, and the structured subrectangle of a leaf $x_{(C,\alpha)}$ is $R_{C,\alpha}$ itself, with the restriction falsifying $C$ (printed pp. 23–24: the scheme applied to $R_{C,\alpha}$ outputs $R_{C,\alpha}$ as the single member of the partition).
--
--   These definitions turn the dag-like lifting framework of [GGKS20] into an approximation model; the mission's results are stated for every scheme with the Lemma 4.7 properties.
--
--   **Formalization Note** Min-entropy is in bits: condition 2 says every value of $\mathbf X_I$ has probability at most $m^{-0.9|I|}$, condition 3 that $|Y|\ge 2^{mn-n^3}$. "$O(w)$" is $Kw$ for a constant $K$ fixed before $n$. The scheme is an arbitrary deterministic function satisfying the properties (`IsRectangleScheme`); its existence is Lemma 4.7. A restriction is `Fin n → Option Bool` from the published CNF definition.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Definition 4.6 (printed p. 20, PDF p. 21), Lemma 4.7 (printed p. 21, PDF p. 22), Definition 4.9 (printed pp. 21–22, PDF pp. 22–23), §4.4 (printed p. 23, PDF p. 24)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover

noncomputable section

namespace LimitsLifting.Approximation

open Classical
open MultiplierAssoc206.Resolution

/-! # Structured rectangles, the Rectangle Scheme interface and the approximation model `M_w`

Carenini, Cavalar, Grosser, Pich, *Limits of Lifting*, STOC 2027 submission #309,
§4.2 (Definition 4.6, Lemma 4.7; printed pp. 20–21, PDF pp. 21–22), §4.3 (Definition 4.9;
printed pp. 21–22, PDF pp. 22–23) and §4.4 (ρ-like rectangles, rectangle circuits;
printed pp. 23–24, PDF pp. 24–25).

A restriction `ρ ∈ {0,1,*}^n` is `Restriction (Fin n) = Fin n → Option Bool` from the published
CNF definition: `ρ i = some b` fixes coordinate `i` to `b`, `ρ i = none` leaves it free. -/

section Restrictions

variable {n : ℕ}

/-- `fix(ρ)`, the fixed coordinates of a restriction. -/
def fixSet (ρ : Restriction (Fin n)) : Finset (Fin n) := Finset.univ.filter (fun i => (ρ i).isSome)

/-- The width `|fix(ρ)|` of a restriction. -/
def restrWidth (ρ : Restriction (Fin n)) : ℕ := (fixSet ρ).card

/-- `z ∈ C_ρ⁻¹(1)`: the string `z ∈ {0,1}^n` is consistent with `ρ`. -/
def ConsistentWith (ρ : Restriction (Fin n)) (z : Fin n → Bool) : Prop :=
  ∀ i b, ρ i = some b → z i = b

/-- The restriction that sets the variables of the clause `C` so as to falsify it and leaves
everything else free (Proposition 4.14). For a non-tautological clause, `C_ρ⁻¹(1) = C⁻¹(0)`. -/
def falsifyingRestriction (C : Clause (Fin n)) : Restriction (Fin n) := fun i =>
  if (i, true) ∈ C then some false else if (i, false) ∈ C then some true else none

end Restrictions

section Structured

variable {n m : ℕ}

/-- A nonempty rectangle `X × Y ⊆ [m]^n × {0,1}^{mn}` is **ρ-structured** (Definition 4.6) if
1. `X_{fix(ρ)}` is fixed and every `z ∈ G(X × Y)` is consistent with `ρ`;
2. for every nonempty `I ⊆ free(ρ)`, the marginal of the uniform distribution on `X` satisfies
   `H∞(X_I) ≥ 0.9 |I| log m`, i.e. every value `a ∈ [m]^I` has probability `≤ m^{-0.9|I|}`;
3. `H∞(Y) ≥ mn − n³`, i.e. `|Y| ≥ 2^{mn − n³}`.
Min-entropies are in bits. -/
def IsStructured (ρ : Restriction (Fin n)) (X : Finset (AliceIn n m)) (Y : Finset (BobIn n m)) :
    Prop :=
  X.Nonempty ∧ Y.Nonempty ∧
  (∀ x ∈ X, ∀ x' ∈ X, ∀ i ∈ fixSet ρ, x i = x' i) ∧
  (∀ x ∈ X, ∀ y ∈ Y, ConsistentWith ρ (gadget x y)) ∧
  (∀ I : Finset (Fin n), I.Nonempty → (∀ i ∈ I, ρ i = none) → ∀ a : Fin n → Fin m,
    ((X.filter (fun x => ∀ i ∈ I, x i = a i)).card : ℝ) ≤
      (X.card : ℝ) * (m : ℝ) ^ (-(9 / 10 : ℝ) * (I.card : ℝ))) ∧
  (2 : ℝ) ^ ((m : ℝ) * n - (n : ℝ) ^ 3) ≤ (Y.card : ℝ)

/-- A rectangle `X × Y` is **ρ-like** (§4.4) if its image under `G = Ind_m^n` is exactly the
subcube `C_ρ⁻¹(1)` of strings consistent with `ρ`. -/
def IsLike (ρ : Restriction (Fin n)) (X : Finset (AliceIn n m)) (Y : Finset (BobIn n m)) : Prop :=
  ∀ z : Fin n → Bool, (∃ x ∈ X, ∃ y ∈ Y, gadget x y = z) ↔ ConsistentWith ρ z

end Structured

section Scheme

variable {n m : ℕ}

/-- The output of the Rectangle Scheme on one rectangle: the structured pieces (each with its
restriction `ρ_i`), the error pieces, and the error sets `X_err`, `Y_err`. -/
structure SchemeOutput (n m : ℕ) where
  structured : Finset (Restriction (Fin n) × Finset (AliceIn n m) × Finset (BobIn n m))
  errorPieces : Finset (Finset (AliceIn n m) × Finset (BobIn n m))
  Xerr : Finset (AliceIn n m)
  Yerr : Finset (BobIn n m)

/-- A (deterministic) rectangle scheme: for each parameter `w` and rectangle `S × T`, an
output. -/
abbrev RectScheme (n m : ℕ) :=
  ℝ → Finset (AliceIn n m) → Finset (BobIn n m) → SchemeOutput n m

/-- Two rectangles are disjoint. -/
def RectDisjoint (P Q : Finset (AliceIn n m) × Finset (BobIn n m)) : Prop :=
  Disjoint P.1 Q.1 ∨ Disjoint P.2 Q.2

/-- The properties of the Rectangle Scheme stated in Lemma 4.7, with `O(w)` instantiated as
`K * w` for the constant `K`: for every parameter `0 < w ≤ n` and every rectangle `S × T`,
the output pieces are nonempty, contained in `S × T`, pairwise disjoint and cover `S × T`
(a partition); `X_err` and `Y_err` have densities `≤ n^{-w}`; each structured piece is
`ρ_i`-structured with `|fix(ρ_i)| ≤ K w`; each error piece lies in
`X_err × {0,1}^{mn} ∪ [m]^n × Y_err`; and query alignment holds: for every `x ∉ X_err` there is
`I_x ⊆ [n]`, `|I_x| ≤ K w`, with `fix(ρ_i) ⊆ I_x` for every structured piece meeting
`{x} × {0,1}^{mn}`. -/
def IsRectangleScheme (n m : ℕ) (K : ℝ) (σ : RectScheme n m) : Prop :=
  ∀ w : ℝ, 0 < w → w ≤ n → ∀ (S : Finset (AliceIn n m)) (T : Finset (BobIn n m)),
    -- the structured pieces are nonempty, inside `S × T`, pairwise disjoint
    (∀ p ∈ (σ w S T).structured, p.2.1.Nonempty ∧ p.2.2.Nonempty ∧ p.2.1 ⊆ S ∧ p.2.2 ⊆ T) ∧
    (∀ q ∈ (σ w S T).errorPieces, q.1.Nonempty ∧ q.2.Nonempty ∧ q.1 ⊆ S ∧ q.2 ⊆ T) ∧
    (∀ p ∈ (σ w S T).structured, ∀ p' ∈ (σ w S T).structured, p ≠ p' →
      RectDisjoint p.2 p'.2) ∧
    (∀ q ∈ (σ w S T).errorPieces, ∀ q' ∈ (σ w S T).errorPieces, q ≠ q' → RectDisjoint q q') ∧
    (∀ p ∈ (σ w S T).structured, ∀ q ∈ (σ w S T).errorPieces, RectDisjoint p.2 q) ∧
    -- the pieces cover `S × T`
    (∀ x ∈ S, ∀ y ∈ T, (∃ p ∈ (σ w S T).structured, x ∈ p.2.1 ∧ y ∈ p.2.2) ∨
      (∃ q ∈ (σ w S T).errorPieces, x ∈ q.1 ∧ y ∈ q.2)) ∧
    -- error sets of density at most `n^{-w}`
    aliceDensity (σ w S T).Xerr ≤ (n : ℝ) ^ (-w) ∧
    bobDensity (σ w S T).Yerr ≤ (n : ℝ) ^ (-w) ∧
    -- structured case
    (∀ p ∈ (σ w S T).structured, IsStructured p.1 p.2.1 p.2.2 ∧ (restrWidth p.1 : ℝ) ≤ K * w) ∧
    -- error case
    (∀ q ∈ (σ w S T).errorPieces, ∀ x ∈ q.1, ∀ y ∈ q.2,
      x ∈ (σ w S T).Xerr ∨ y ∈ (σ w S T).Yerr) ∧
    -- query alignment
    (∀ x : AliceIn n m, x ∉ (σ w S T).Xerr → ∃ I : Finset (Fin n), (I.card : ℝ) ≤ K * w ∧
      ∀ p ∈ (σ w S T).structured, x ∈ p.2.1 → p.2.2.Nonempty → fixSet p.1 ⊆ I)

end Scheme

section Model

variable {n m : ℕ} {F : CNF (Fin n)}

/-- The approximating gate `g ∘̄ h` of Definition 4.9 for `∘ = ∧` (`isAnd = true`) or `∨`:
if `g` or `h` is one of the constant functions `0, 1`, it is the exact gate `g ∘ h`; otherwise,
with `X_err`, `Y_err` the error sets of the scheme (parameter `w`) on `R_{g∘h}`, it agrees with
`g ∘ h` except that it equals `0` on `A(X_err)` and `1` on `B(Y_err)`. -/
noncomputable def approxOp (σ : RectScheme n m) (w : ℝ) (isAnd : Bool)
    (g h : liftDomain m F → Bool) : liftDomain m F → Bool :=
  let op : Bool → Bool → Bool := if isAnd then (· && ·) else (· || ·)
  let exact : liftDomain m F → Bool := fun z => op (g z) (h z)
  if g = (fun _ => false) ∨ g = (fun _ => true) ∨ h = (fun _ => false) ∨ h = (fun _ => true)
  then exact
  else
    let e := σ w (rectOf exact).1 (rectOf exact).2
    fun z =>
      if ∃ x ∈ e.Xerr, encA F x = z.1 then false
      else if ∃ y ∈ e.Yerr, encB F y = z.1 then true
      else exact z

/-- `M_w` (Definition 4.9): the partial functions on `Z_{m,n}` computed by `{∨̄, ∧̄}`-circuits
from the input coordinates `x_{(C,α)}` and the constants `0, 1`; i.e. the least set containing
these and closed under the approximating gates. No size bound is imposed. -/
inductive InModel (σ : RectScheme n m) (w : ℝ) : (liftDomain m F → Bool) → Prop
  | input (c : Coord m F) : InModel σ w (inputFn c)
  | zero : InModel σ w (fun _ => false)
  | one : InModel σ w (fun _ => true)
  | and {g h : liftDomain m F → Bool} :
      InModel σ w g → InModel σ w h → InModel σ w (approxOp σ w true g h)
  | or {g h : liftDomain m F → Bool} :
      InModel σ w g → InModel σ w h → InModel σ w (approxOp σ w false g h)

/-- The set `M_w`. -/
def liftModel (σ : RectScheme n m) (w : ℝ) (F : CNF (Fin n)) : Set (liftDomain m F → Bool) :=
  {g | InModel σ w g}

/-- `µ(f, M_w)` for `f = f_{R_{F,Ind_m}}` and the approximation model `⟨M_w, ∨̄, ∧̄⟩`. -/
noncomputable def liftMu (σ : RectScheme n m) (w : ℝ) (F : CNF (Fin n)) : ℝ :=
  muM (liftedFn m F) (liftModel σ w F) (approxOp σ w true) (approxOp σ w false)

/-- `ε_{M_w}(f)`. -/
noncomputable def liftEps (σ : RectScheme n m) (w : ℝ) (F : CNF (Fin n)) : ℝ :=
  epsM (liftedFn m F) (liftModel σ w F)

end Model

section RectangleCircuits

variable {n m : ℕ} {F : CNF (Fin n)}

/-- The functions computed by the gates of a `{∨̄, ∧̄}`-circuit over the inputs `x_{(C,α)}`
(literals are positive in a monotone circuit). -/
noncomputable def approxGateValues (σ : RectScheme n m) (w : ℝ) (B : Circuit (Coord m F)) :
    List (liftDomain m F → Bool) :=
  B.gateValues (fun c b => if b then inputFn c else fun z => !inputFn c z) (fun b _ => b)
    (approxOp σ w true) (approxOp σ w false)

/-- The function computed by an operand of the circuit `B`. -/
noncomputable def approxOperandValue (σ : RectScheme n m) (w : ℝ) (B : Circuit (Coord m F))
    (o : Operand (Coord m F)) : liftDomain m F → Bool :=
  o.value (fun c b => if b then inputFn c else fun z => !inputFn c z) (fun b _ => b)
    (approxGateValues σ w B)

/-- The function computed by the circuit `B`. -/
noncomputable def approxOutput (σ : RectScheme n m) (w : ℝ) (B : Circuit (Coord m F)) :
    liftDomain m F → Bool :=
  approxOperandValue σ w B B.output

/-- The rectangle `R_g^* = R_{h ∘ h'}` of gate `k` of `B` (§4.4), where `h, h'` are the
functions computed at its two operands and `∘` is its exact operation: the rectangle on which
the Rectangle Scheme is run when `g = h ∘̄ h'` is formed. -/
noncomputable def gateStar (σ : RectScheme n m) (w : ℝ) (B : Circuit (Coord m F)) (k : ℕ) :
    Finset (AliceIn n m) × Finset (BobIn n m) :=
  match B.gates[k]? with
  | some g => rectOf (fun z => (if g.1 then (· && ·) else (· || ·))
      (approxOperandValue σ w B g.2.1 z) (approxOperandValue σ w B g.2.2 z))
  | none => (∅, ∅)

/-- The structured subrectangles attached to a node of the rectangle circuit `Π_B`: for a leaf
`x_{(C,α)}`, the canonical rectangle `R_{C,α}` itself, with the restriction falsifying `C`
(the source, printed pp. 23–24: "the Rectangle Scheme applied to `R_{C,α}` will output `R_{C,α}`
as the single member of the partition"; leaves are never passed through the scheme in `M_w`,
Definition 4.9, and `R_{C,α}` is structured by Proposition 4.14); for a gate `k`, the scheme's
structured pieces on `R_k^*`. -/
noncomputable def nodeStructuredPieces (σ : RectScheme n m) (w : ℝ) (B : Circuit (Coord m F)) :
    Operand (Coord m F) →
      Finset (Restriction (Fin n) × Finset (AliceIn n m) × Finset (BobIn n m))
  | .lit c _ => {(falsifyingRestriction c.1.1, (canonRect c).1, (canonRect c).2)}
  | .const _ => ∅
  | .gate j => (σ w (gateStar σ w B j).1 (gateStar σ w B j).2).structured

/-- A circuit has no constant operands. -/
def Circuit.ConstantFree {ι : Type} (B : Circuit ι) : Prop :=
  (∀ g ∈ B.gates, (∀ b, g.2.1 ≠ .const b) ∧ (∀ b, g.2.2 ≠ .const b)) ∧ ∀ b, B.output ≠ .const b

/-- No gate of `B` computes one of the constant functions `0, 1` on `Z_{m,n}` (the circuit left
after all constants have been removed, §4.4). -/
def NoConstantGates (σ : RectScheme n m) (w : ℝ) (B : Circuit (Coord m F)) : Prop :=
  ∀ g ∈ approxGateValues σ w B, g ≠ (fun _ => false) ∧ g ≠ (fun _ => true)

/-- A rectangle `S × T` is `γ`-dense if both `S` and `T` are `γ`-dense. -/
def RectDense (γ : ℝ) (R : Finset (AliceIn n m) × Finset (BobIn n m)) : Prop :=
  γ ≤ aliceDensity R.1 ∧ γ ≤ bobDensity R.2

end RectangleCircuits

end LimitsLifting.Approximation

end


