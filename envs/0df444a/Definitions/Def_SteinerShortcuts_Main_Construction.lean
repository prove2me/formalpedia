-- Prove2me | Definitions.Def_SteinerShortcuts_Main_Construction
-- name    : SteinerShortcuts_Main_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:34:23.33579+00:00
-- url     : https://prove2.me/theorems/b16f18cd-85ff-4081-a64e-4d43c92cf60c
-- title:
--   The optimized 21-coordinate graph and its critical paths
-- statement:
--   Fix an even integer $L\ge4$ and a prime $q\in[L,2L]$. Labels $t\in\{0,\ldots,q-1\}$ give directions
--   $$
--   y_t=t^2\bmod q,\qquad z_t=(t^2-y_t)/q,\qquad c_t=(t,y_t,z_t,ty_t).
--   $$
--   A vertex has position $(\ell,r_o,r_e,x_o,x_e)$ with $x_o,x_e\in\mathbb Z^4$, followed by ten augmentation coordinates. Each step raises the layer by one and raises the counter and sum for that layer's parity by $1,c_t$. At every step the augmentation records $y_t^2$; at odd steps it records $(x_o^1,r_ox_o^1,(x_o^1)^2)$ and $(tx_e^1,x_e^1,r_ot)$; at even steps it records $(x_e^1,r_ex_e^1,(x_e^1)^2)$. Other entries are zero, and all expressions use the position before the step. The two triples occupy consecutive odd then even slots.
--
--   Put $X=Lq$, $X'=Lq^2$ and
--   $$
--   (B_1,\ldots,B_7)=(Lq^2,2L^2q,2L^3q,4L^3q^2,2L^2q^2,2L^2q,L^2q).
--   $$
--   The source box is $\{(1,0,0)\}\times([0,X]^3\times[0,X'])^2\times[0,B_1]\times([0,B_2]\times[0,B_3]\times[0,B_4])^2\times[0,B_5]\times[0,B_6]\times[0,B_7]$. Each later layer $\ell\le L$ has counters $\lfloor\ell/2\rfloor,\lfloor(\ell-1)/2\rfloor$ and all free bounds doubled. Intervals are inclusive integer intervals. An edge is included exactly when it is prescribed by the update and both endpoints lie in the vertex set.
--
--   For each source $s$ and labels $a,b$, the critical sequence alternates labels $a,b$ for $L-1$ updates. The critical-path family is the set of actual resulting sequences. Containment, distinctness, uniqueness and overlap are results, not defining conditions. Properties (Q1), (Q2), (Q3) mean respectively restriction to the two labels for each parity, their stated order (reversed on the reverse cross-path), and a single vertex at which both parities switch.
--
--   The infinite family uses $L_k=2k+4$ and the least prime above $L_k$ and at most $2L_k$, chosen independently of every edge budget. Since these $L_k$ are even and at least four, this is also the least prime at least $L_k$. The family graph is restricted to the finite subtype of its actual coordinate vertices, with actual edge counts.
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), pp. 8, 16, 21–22, eqs. (2), (6), (11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Graphs

namespace SteinerShortcuts.Main

noncomputable section
open scoped Classical

abbrev Point := Fin 21 → ℤ
abbrev Position := Fin 11 → ℤ
abbrev Direction := Fin 4 → ℤ

def position (v : Point) : Position := fun i => v ⟨i.val, by omega⟩

def labelY (q t : ℕ) : ℤ := (t : ℤ) ^ 2 % (q : ℤ)

def direction (q : ℕ) (t : Fin q) : Direction :=
  ![(t.val : ℤ), labelY q t.val,
    ((t.val : ℤ) ^ 2 - labelY q t.val) / (q : ℤ), (t.val : ℤ) * labelY q t.val]

def directions (q : ℕ) : Finset Direction := Finset.univ.image (direction q)

def AverageFree (C : Finset Direction) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ c₀ ∈ C, ∀ cs : Fin k → Direction,
    (∀ i, cs i ∈ C) → (k : ℤ) • c₀ = ∑ i, cs i → ∀ i, cs i = c₀

/-- The complete 21-coordinate update (2), with the ten augmentation
coordinates in the source order on printed page 21. All entries use pre-step p. -/
def update (q : ℕ) (p : Position) (t : Fin q) : Point :=
  let c := direction q t
  let odd := p 0 % 2 = 1
  let o : ℤ := if odd then 1 else 0
  let e : ℤ := if odd then 0 else 1
  ![1, o, e,
    o * c 0, o * c 1, o * c 2, o * c 3,
    e * c 0, e * c 1, e * c 2, e * c 3,
    (labelY q t.val)^2,
    o * p 3, o * (p 1 * p 3), o * (p 3)^2,
    e * p 7, e * (p 2 * p 7), e * (p 7)^2,
    o * ((t.val : ℤ) * p 7), o * p 7, o * (p 1 * (t.val : ℤ))]

def step (q : ℕ) (v : Point) (t : Fin q) : Point := v + update q (position v) t

/-- Free-coordinate bounds, ordered odd triple then even triple. -/
def boxBounds (L q : ℕ) : Point :=
  let l : ℤ := L
  let p : ℤ := q
  ![0, 0, 0,
    l*p, l*p, l*p, l*p^2, l*p, l*p, l*p, l*p^2,
    l*p^2,
    2*l^2*p, 2*l^3*p, 4*l^3*p^2,
    2*l^2*p, 2*l^3*p, 4*l^3*p^2,
    2*l^2*p^2, 2*l^2*p, l^2*p]

/-- A layer box; scale=1 is S and scale=2 is used at later layers. -/
def layerBox (L q ell : ℕ) (scale : ℤ) : Finset Point :=
  Fintype.piFinset fun i =>
    if i = 0 then {(ell : ℤ)}
    else if i = 1 then {((ell / 2 : ℕ) : ℤ)}
    else if i = 2 then {(((ell - 1) / 2 : ℕ) : ℤ)}
    else Finset.Icc 0 (scale * boxBounds L q i)

def sources (L q : ℕ) : Finset Point := layerBox L q 1 1

def vertices (L q : ℕ) : Finset Point :=
  sources L q ∪ (Finset.Icc 2 L).biUnion (fun ell => layerBox L q ell 2)

def construction (L q : ℕ) : Digraph Point where
  Adj v w := v ∈ vertices L q ∧ w ∈ vertices L q ∧ v 0 < (L : ℤ) ∧
    ∃ t : Fin q, w = step q v t

/-- Critical vertices are computed, without any containment or uniqueness certificate. -/
def criticalVertex (q : ℕ) (s : Point) (a b : Fin q) : ℕ → Point
  | 0 => s
  | i + 1 => step q (criticalVertex q s a b i) (if i % 2 = 0 then a else b)

def critical (L q : ℕ) (s : Point) (a b : Fin q) : Route Point :=
  ⟨s, (List.range (L - 1)).map fun i => criticalVertex q s a b (i + 1)⟩

def criticalPaths (L q : ℕ) : Finset (Route Point) :=
  (sources L q ×ˢ ((Finset.univ : Finset (Fin q)) ×ˢ
    (Finset.univ : Finset (Fin q)))).image fun sab => critical L q sab.1 sab.2.1 sab.2.2

def constructionEdges (L q : ℕ) : Finset (Point × Point) :=
  (vertices L q ×ˢ vertices L q).filter fun e => (construction L q).Adj e.1 e.2

def Admissible (L q : ℕ) : Prop := 4 ≤ L ∧ Even L ∧ Nat.Prime q ∧ L ≤ q ∧ q ≤ 2*L

/-- Parameters for a critical path; membership in S is stated separately. -/
structure CriticalData (q : ℕ) where
  source : Point
  a : Fin q
  b : Fin q

def CriticalData.route {q : ℕ} (P : CriticalData q) (L : ℕ) : Route Point :=
  critical L q P.source P.a P.b

def CriticalData.Valid {q : ℕ} (P : CriticalData q) (L : ℕ) : Prop :=
  P.source ∈ sources L q

/-- The step label is extracted from the first updated position coordinate.
For a genuine edge it is a unique member of Fin q; this is not assumed here. -/
def edgeLabel (v w : Point) : ℤ :=
  if v 0 % 2 = 1 then w 3 - v 3 else w 7 - v 7

def UsesLabel (R : Route Point) (i : ℕ) (t : ℤ) : Prop :=
  ∃ v w, R.vertices[i]? = some v ∧ R.vertices[i+1]? = some w ∧ edgeLabel v w = t

def OddStep (R : Route Point) (i : ℕ) : Prop :=
  ∃ v, R.vertices[i]? = some v ∧ v 0 % 2 = 1

def EvenStep (R : Route Point) (i : ℕ) : Prop :=
  ∃ v, R.vertices[i]? = some v ∧ v 0 % 2 = 0

/-- Q1 includes every actual step, with parity referring to the source layer. -/
def Q1 {q : ℕ} (P Q : CriticalData q) (R : Route Point) : Prop :=
  ∀ i < R.length,
    (OddStep R i → UsesLabel R i P.a.val ∨ UsesLabel R i Q.a.val) ∧
    (EvenStep R i → UsesLabel R i P.b.val ∨ UsesLabel R i Q.b.val)

def LabelsOrdered (R : Route Point) (odd : Bool) (a b : ℤ) : Prop :=
  ∀ i < R.length, ∀ j < R.length,
    (if odd then OddStep R i ∧ OddStep R j else EvenStep R i ∧ EvenStep R j) →
    UsesLabel R i a → UsesLabel R j b → i < j

/-- Equal labels impose no ordering requirement, as in the source's equal-label cases. -/
def Q2 {q : ℕ} (P Q : CriticalData q) (R : Route Point) : Prop :=
  (P.a ≠ Q.a → LabelsOrdered R true P.a.val Q.a.val) ∧
  (P.b ≠ Q.b → LabelsOrdered R false P.b.val Q.b.val)

def Follows {q : ℕ} (P : CriticalData q) (R : Route Point) (i : ℕ) : Prop :=
  (OddStep R i → UsesLabel R i P.a.val) ∧
  (EvenStep R i → UsesLabel R i P.b.val)

/-- Q3 chooses a vertex index, allowing the switch at either endpoint. -/
def Q3 {q : ℕ} (P Q : CriticalData q) (R : Route Point) : Prop :=
  ∃ j ≤ R.length, (∀ i < j, Follows P R i) ∧
    ∀ i, j ≤ i → i < R.length → Follows Q R i

/-- Restrict the ambient construction to its actual finite vertex set. -/
abbrev Vertex (L q : ℕ) := ↥(vertices L q)

def finiteConstruction (L q : ℕ) : Digraph (Vertex L q) where
  Adj v w := (construction L q).Adj v.val w.val

/-- Least admissible prime, chosen once from L, independently of the edge budget.
On L=0 the harmless default is 2; the mission only uses L≥4. -/
def chosenPrime (L : ℕ) : ℕ :=
  if h : L ≠ 0 then Nat.find (Nat.exists_prime_lt_and_le_two_mul L h) else 2

def familyLayers (k : ℕ) : ℕ := 2*k+4

def familyPrime (k : ℕ) : ℕ := chosenPrime (familyLayers k)

abbrev FamilyVertex (k : ℕ) := Vertex (familyLayers k) (familyPrime k)

def familyGraph (k : ℕ) : Digraph (FamilyVertex k) :=
  finiteConstruction (familyLayers k) (familyPrime k)

end
end SteinerShortcuts.Main


