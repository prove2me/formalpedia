-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_Rho
-- name    : MultiplierAssoc206_Resolution_Rho
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:19:08.117193+00:00
-- url     : https://prove2.me/theorems/8623107f-4fbb-4b70-a3f5-d32dd47af925
-- title:
--   The restriction $\rho$, the propagated assignment $\bar\alpha$, edge- and star-locality, and the support of a clause
-- statement:
--   Fix a family $(\mathrm{Mul}_n)_n$, a bit-width $n$, a bipartite graph $H=(U,V,E)$ and index maps $i,j,k$ for $H$ with strip width $g$ (Lemma 7.3). The unset input bit $y_{j(e)}$ is identified with the edge variable $X_e$.
--
--   **The restriction $\rho$ (Definition 7.4).**
--   (a) $\rho$ sets $x_{i(u)}=1$ for $u\in U$ and $z_{k(v)}=1$ for $v\in V$, leaves $y_{j(e)}$ unset for $e\in E$, and sets every other bit of $x,y,z$ to $0$.
--   (b) For each $v\in V$, $\rho$ sets the output of the $g$-strip of $xy$ with base $\mathrm{col}_{\mathbf{xy}}(v)$ to the binary representation of $1$ (bit $1$ in column $\mathrm{col}_{\mathbf{xy}}(v)$, bit $0$ in the other $g-1$ columns), leaves the output bit in column $\mathrm{col}_{\mathbf{xy}}(u,e)$ unset for each non-incident pair $(u,e)$, and sets every other output bit of $xy$ to $0$; symmetrically for $yz$ with the strips at $\mathrm{col}_{\mathbf{yz}}(u)$ and the non-incident pairs $(e,v)$. All other wires are unset.
--   (c) $\rho$ sets the miter variable $e_K=1$.
--
--   The restriction induces input restrictions of the four multipliers: $(x,y)$ for $xy$, $(y,z)$ for $yz$, (output wires of $xy$, zero-padded $z$) for $(xy)z$, and (zero-padded $x$, output wires of $yz$) for $x(yz)$.
--
--   **Propagated assignment (Definition 8.1).** For an assignment $\alpha$ of the edge variables, $\bar\alpha$ extends $\rho$ and gives every other variable the value of its Boolean function at $\alpha$: an unset wire of an inner multiplier takes its function's value at the inputs $x,y,z$ determined by $\rho$ and $\alpha$; a wire of an outer multiplier takes its function's value at its input bits, which are the values $\bar\alpha$ gives the inner output wires (the constants of $\rho$, or the function value where $\rho$ leaves the bit unset) and the zero-padded $x$ or $z$; an unset miter variable is the XOR of the two outer output bits. Each variable $q$ thus computes a Boolean function $\alpha\mapsto\bar\alpha(q)$ of the edge variables.
--
--   **Edge- and star-local (Definition 8.2).** A function of the edge variables is **edge-local** if it is not constant and depends on a single edge variable; it is **star-local at $w$** if it is neither constant nor edge-local and is a function of $\{X_e:e\in E(w)\}$.
--
--   **Support (Definition 8.3).** The support $\mathrm{supp}(C)$ of a clause $C$ of $\mathsf{Assoc}_n{\restriction_\rho}$ is the set of vertices $w\in U\cup V$ such that some variable of $C$ depends on an edge variable of the star $E(w)$; "depends" is semantic: flipping that edge variable changes the variable's value for some $\alpha$.
--
--   **Formalization Note** The inner output wire for bit $c$ is located through the output map of the encoding; for an exact encoding with $n\ge1$ distinct output bits are distinct wires. $\mathrm{ExactOne}(X_{E(w)})$ is satisfied by $\alpha$ when exactly one edge of $E(w)$ is set to true.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.18–19 (printed pp.17–18), Definition 7.4 (PDF p.18), Definitions 8.1–8.3 (PDF p.19)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Assoc
import Definitions.Def_MultiplierAssoc206_Resolution_IndexMaps

namespace MultiplierAssoc206.Resolution

open Classical

/-! # The restriction `ρ`, the propagated assignment, locality and support

Liew, *Associativity of Multiplication Is Hard for Resolution*, Definition 7.4 (PDF p. 18) and
Definitions 8.1–8.3 (PDF p. 19). Throughout, `Mul` is a family of multiplier encodings, `n` the
bit-width of `Assoc_n`, `H = (U, V, E)` a bipartite graph, and `M` index maps for `H` with strip
width `g` and bound `n₀` (the properties of Lemma 7.3). The unset input bit `y_{j(e)}` is the
edge variable `X_e`. -/

variable (Mul : (n : ℕ) → MulEncoding n) (n : ℕ) {U V : Type} [Fintype U] [Fintype V]
  {E : Finset (U × V)} {g n₀ : ℕ} (M : IndexMaps E g n₀)

/-- Definition 7.4(b), multiplier `xy`: the value `ρ` gives the inner output bit in column `c`.
The `g`-strip with base `col_xy(v)` is set to the binary representation of `1` (bit `1` at the
base, `0` at the other `g − 1` columns of the strip); the bit in column `col_xy(u, e)` of each
non-incident pair `(u, e)` is left unset; every other output bit is set to `0`. -/
noncomputable def rhoInnerXY (c : ℕ) : Option Bool :=
  if ∃ v, M.cxy v = c then some true
  else if ∃ v, M.cxy v < c ∧ c < M.cxy v + g then some false
  else if ∃ (u : U) (e : Edge E), u ≠ e.1.1 ∧ M.i u + M.j e = c then none
  else some false

/-- Definition 7.4(b), multiplier `yz`: symmetric to `rhoInnerXY`, with the strips at
`col_yz(u)` and the columns `col_yz(e, v)` of the non-incident pairs `(e, v)`. -/
noncomputable def rhoInnerYZ (c : ℕ) : Option Bool :=
  if ∃ u, M.cyz u = c then some true
  else if ∃ u, M.cyz u < c ∧ c < M.cyz u + g then some false
  else if ∃ (e : Edge E) (v : V), v ≠ e.1.2 ∧ M.j e + M.k v = c then none
  else some false

/-- Definition 7.4 (The restriction `ρ`) on the variables of `Assoc_n`.
(a) `x_{i(u)} = 1`, `z_{k(v)} = 1`, `y_{j(e)}` unset (it is `X_e`), all other input bits `0`;
(b) the output wires of `xy` and `yz` as in `rhoInnerXY`, `rhoInnerYZ`; the other wires of all
four multipliers unset; (c) the miter variable `e_K = 1`, the other miter variables unset. -/
noncomputable def rho : Restriction (AVar Mul n) := fun q =>
  match q with
  | .x i => some (decide (∃ u, M.i u = (i : ℕ)))
  | .y i => if ∃ e, M.j e = (i : ℕ) then none else some false
  | .z i => some (decide (∃ v, M.k v = (i : ℕ)))
  | .xy w =>
      if h : ∃ c : Fin (2 * n), (Mul n).out c = w then rhoInnerXY M ((Classical.choose h : Fin (2 * n)) : ℕ)
      else none
  | .yz w =>
      if h : ∃ c : Fin (2 * n), (Mul n).out c = w then rhoInnerYZ M ((Classical.choose h : Fin (2 * n)) : ℕ)
      else none
  | .xy_z _ => none
  | .x_yz _ => none
  | .e i => if (i : ℕ) = M.K then some true else none

/-- The restriction `ρ` induces on the inputs `(x, y)` of the inner multiplier `xy`. -/
noncomputable def restrXY : InputRestr n :=
  (fun i => rho Mul n M (.x i), fun i => rho Mul n M (.y i))

/-- The restriction `ρ` induces on the inputs `(y, z)` of the inner multiplier `yz`. -/
noncomputable def restrYZ : InputRestr n :=
  (fun i => rho Mul n M (.y i), fun i => rho Mul n M (.z i))

/-- The restriction `ρ` induces on the inputs `(xy, z)` of the outer multiplier `(xy)z`:
input bit `k` of `xy` is the output wire `k` of `xy`; `z` is zero-padded to `2n` bits. -/
noncomputable def restrXYZ : InputRestr (2 * n) :=
  (fun k => rho Mul n M (.xy ((Mul n).out k)),
   fun k => if h : (k : ℕ) < n then rho Mul n M (.z ⟨k, h⟩) else some false)

/-- The restriction `ρ` induces on the inputs `(x, yz)` of the outer multiplier `x(yz)`:
`x` is zero-padded to `2n` bits; input bit `k` of `yz` is the output wire `k` of `yz`. -/
noncomputable def restrXYZ' : InputRestr (2 * n) :=
  (fun k => if h : (k : ℕ) < n then rho Mul n M (.x ⟨k, h⟩) else some false,
   fun k => rho Mul n M (.yz ((Mul n).out k)))

/-- The variable `q` of `Assoc_n` is a circuit wire (of one of the four multipliers) or a miter
variable, not an input bit. -/
def IsWireOrMiter {W₁ W₂ : Type} {n : ℕ} : AssocVar W₁ W₂ n → Prop
  | .x _ => False
  | .y _ => False
  | .z _ => False
  | _ => True

section Propagate

variable (α : Edge E → Bool)

/-- The input bit-vector `x` under `ρ`. -/
noncomputable def propX : Fin n → Bool := fun i => decide (∃ u, M.i u = (i : ℕ))

/-- The input bit-vector `y` under `ρ` and the edge assignment `α` (`y_{j(e)} = α(X_e)`). -/
noncomputable def propY : Fin n → Bool := fun i =>
  if h : ∃ e, M.j e = (i : ℕ) then α (Classical.choose h) else false

/-- The input bit-vector `z` under `ρ`. -/
noncomputable def propZ : Fin n → Bool := fun i => decide (∃ v, M.k v = (i : ℕ))

/-- Value of a wire of `xy`: `ρ`'s value where `ρ` sets it, otherwise its function at the
inputs. -/
noncomputable def propXYWire (w : (Mul n).W) : Bool :=
  match rho Mul n M (.xy w) with
  | some b => b
  | none => (Mul n).fn w (propX n M) (propY n M α)

/-- Value of a wire of `yz`: `ρ`'s value where `ρ` sets it, otherwise its function at the
inputs. -/
noncomputable def propYZWire (w : (Mul n).W) : Bool :=
  match rho Mul n M (.yz w) with
  | some b => b
  | none => (Mul n).fn w (propY n M α) (propZ n M)

/-- Value of a wire of `(xy)z`: its function at its input bits, which are the (propagated)
output wires of `xy` and the zero-padded `z`. -/
noncomputable def propXYZWire (w : (Mul (2 * n)).W) : Bool :=
  (Mul (2 * n)).fn w (fun k => propXYWire Mul n M α ((Mul n).out k))
    (fun k => if h : (k : ℕ) < n then propZ n M ⟨k, h⟩ else false)

/-- Value of a wire of `x(yz)`: its function at its input bits, which are the zero-padded `x`
and the (propagated) output wires of `yz`. -/
noncomputable def propXYZ'Wire (w : (Mul (2 * n)).W) : Bool :=
  (Mul (2 * n)).fn w (fun k => if h : (k : ℕ) < n then propX n M ⟨k, h⟩ else false)
    (fun k => propYZWire Mul n M α ((Mul n).out k))

/-- Definition 8.1 (Propagated assignment) `ᾱ`: it extends `ρ` and gives every variable of
`Assoc_n↾ρ` the value of its Boolean function of the edge variables at `α`. -/
noncomputable def propagate : AVar Mul n → Bool := fun q =>
  match q with
  | .x i => propX n M i
  | .y i => propY n M α i
  | .z i => propZ n M i
  | .xy w => propXYWire Mul n M α w
  | .yz w => propYZWire Mul n M α w
  | .xy_z w => propXYZWire Mul n M α w
  | .x_yz w => propXYZ'Wire Mul n M α w
  | .e i =>
      match rho Mul n M (.e i) with
      | some b => b
      | none =>
          xor (propXYZWire Mul n M α ((Mul (2 * n)).out ⟨i, by have := i.2; omega⟩))
            (propXYZ'Wire Mul n M α ((Mul (2 * n)).out ⟨i, by have := i.2; omega⟩))

end Propagate

section Locality

/-- The Boolean function of the edge variables that the variable `q` computes under `ρ`. -/
noncomputable def varFun (q : AVar Mul n) : (Edge E → Bool) → Bool :=
  fun α => propagate Mul n M α q

/-- `F` is constant. -/
def IsConstFn (F : (Edge E → Bool) → Bool) : Prop := ∀ α α', F α = F α'

/-- `F` is a Boolean function of the edge variables `{X_e : e ∈ S}`. -/
def FunOf (F : (Edge E → Bool) → Bool) (S : Finset (Edge E)) : Prop :=
  ∀ α α', (∀ e ∈ S, α e = α' e) → F α = F α'

/-- Definition 8.2: edge-local — not constant, and a function of a single edge variable. -/
def IsEdgeLocal (F : (Edge E → Bool) → Bool) : Prop :=
  ¬ IsConstFn F ∧ ∃ e, FunOf F {e}

/-- Definition 8.2: star-local at `w` — neither constant nor edge-local, and a function of
`{X_e : e ∈ E(w)}`. -/
def IsStarLocalAt (F : (Edge E → Bool) → Bool) (w : U ⊕ V) : Prop :=
  ¬ IsConstFn F ∧ ¬ IsEdgeLocal F ∧ FunOf F (star E w)

/-- `F` depends on the edge variable `X_e` (semantically). -/
def DependsOnEdge (F : (Edge E → Bool) → Bool) (e : Edge E) : Prop :=
  ∃ α : Edge E → Bool, F α ≠ F (Function.update α e (!α e))

/-- Definition 8.3 (Support of a restricted clause): the vertices `w ∈ U ∪ V` such that some
variable of `C` depends on an edge variable of the star `E(w)`. -/
noncomputable def supp (C : Clause (AVar Mul n)) : Finset (U ⊕ V) :=
  Finset.univ.filter fun w =>
    ∃ l ∈ C, ∃ e ∈ star E w, DependsOnEdge (varFun Mul n M l.1) e

/-- The edge assignment `α` sets exactly one edge variable of the star `E(w)` to true, i.e. it
satisfies `ExactOne(X_{E(w)})`. -/
def ExactlyOneAt (α : Edge E → Bool) (w : U ⊕ V) : Prop :=
  ((star E w).filter fun e => α e = true).card = 1

end Locality

end MultiplierAssoc206.Resolution


