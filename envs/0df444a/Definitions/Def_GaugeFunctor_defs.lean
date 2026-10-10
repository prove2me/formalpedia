-- Prove2me | Definitions.Def_GaugeFunctor_defs
-- name    : GaugeFunctor_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-09T23:02:58.937559+00:00
-- url     : https://prove2.me/theorems/016e3f76-bd44-4f4a-bfa3-ce39b137fb49
-- title:
--   Gauge theory on a finite graph: connections, gauge groupoid, holonomy maps and functors
-- statement:
--   A finite directed graph $X$ (vertices $V=\{0,\dots,n_V-1\}$, edges $E$, maps $\mathrm{src},\mathrm{tgt}:E	o V$); steps (an edge traversed forwards or backwards), walks from $x$ to $y$, and connectivity from a vertex $x$. For a group $G$: connections $A:E	o G$, their holonomy $\mathrm{hol}_A(w)$ along walks, and the gauge action $(g\cdot A)(e)=g(\mathrm{src}\,e)A(e)g(\mathrm{tgt}\,e)^{-1}$ of $g:V	o G$, with the covariance $\mathrm{hol}_{g\cdot A}(w)=g(x)\,\mathrm{hol}_A(w)\,g(y)^{-1}$ for a walk $x	o y$ (proved). The category $\mathsf{Pot}_G(X)$ of connections with gauge arrows; the category $\mathsf{Hol}_x$ of holonomy maps at $x$ (multiplicative on loops at $x$, invariant under inserting a backtrack) with conjugation arrows; the functors $\mathrm{hol}_x$ ($A\mapsto\mathrm{hol}_A$, $g\mapsto g(x)$) and $\mathrm{orb}$ (to the discrete category of gauge orbits); 2-complexes (graphs with faces, each with a base vertex and a boundary loop) and the curvature functor $\mathrm{curv}_Y$ (conjugacy classes of face holonomies, into a discrete category); and the examples: the triangle graph, its face-free version $\partial\Delta$ (a circle) and the filled triangle $\Delta$.
-- source:
--   J. C. Baez, Spin network states in gauge theory, Adv. Math. 117 (1996) 253-272, https://arxiv.org/abs/gr-qc/9411007, §2 (gauge theory on a graph); S. Rosenstock, J. O. Weatherall, A categorical equivalence between generalized holonomy maps on a connected manifold and principal connections on bundles over that manifold, J. Math. Phys. 57 (2016) 102902, https://arxiv.org/abs/1504.02401, pp. 2-3 (generalized holonomy maps); J. Nguyen, N. J. Teh, L. Wells, Why surplus structure is not superfluous, Brit. J. Phil. Sci. 71 (2020), https://arxiv.org/abs/1712.01228, §3.2 (the groupoid of gauge fields with gauge arrows)

import Mathlib

/-!
# Non-abelian lattice gauge theory on a finite graph, as categories

Discrete setting for the gauge-functor classification. A finite directed graph carries
`G`-valued connections (one group element per edge, as in Baez, "Spin network states in
gauge theory", Adv. Math. 117 (1996), §2) and gauge transformations (one group element per
vertex).

* `PotG X G`   — connections with gauge transformations as arrows (the groupoid `CA` of
  Nguyen–Teh–Wells, arXiv:1712.01228, §3.2; Weatherall's EM3, arXiv:1505.02229).
* `HolMap X G x`, `HolCat` — generalized holonomy maps at a base vertex `x`: multiplicative on
  loops and invariant under inserting a backtrack (discrete thin equivalence), with
  conjugations as arrows (Rosenstock–Weatherall, arXiv:1504.02401, §I–II).
* `holF : PotG ⥤ HolMap`  — `A ↦ hol A`, `g ↦ g x`.
* `orbitF : PotG ⥤ Discrete (gauge orbits)` — the functor `Γ` of Nguyen–Teh–Wells.
* `curvF : PotG ⥤ Discrete (faces → conjugacy classes)` — the non-abelian field strength of
  a 2-complex: the conjugacy class of the holonomy around each face.
-/

open CategoryTheory

namespace GaugeFunctor

/-- A finite directed graph: `nV` vertices, `nE` edges, edge `e` runs from `src e` to `tgt e`. -/
structure Graph where
  nV : ℕ
  nE : ℕ
  src : Fin nE → Fin nV
  tgt : Fin nE → Fin nV

namespace Graph

variable (X : Graph)

/-- A step of a walk: an edge traversed forwards (`true`) or backwards (`false`). -/
abbrev Step := Fin X.nE × Bool

/-- Start vertex of a step. -/
def stepSrc (s : X.Step) : Fin X.nV := if s.2 then X.src s.1 else X.tgt s.1

/-- End vertex of a step. -/
def stepTgt (s : X.Step) : Fin X.nV := if s.2 then X.tgt s.1 else X.src s.1

/-- The same edge traversed in the opposite direction. -/
def flip (s : X.Step) : X.Step := (s.1, !s.2)

/-- `IsPath x w y`: the list of steps `w` is a walk from vertex `x` to vertex `y`. -/
def IsPath : Fin X.nV → List X.Step → Fin X.nV → Prop
  | x, [], y => x = y
  | x, s :: w, y => X.stepSrc s = x ∧ IsPath (X.stepTgt s) w y

/-- Every vertex can be reached from `x` by a walk (edges may be used in either direction). -/
def Connected (x : Fin X.nV) : Prop := ∀ y, ∃ w, X.IsPath x w y

end Graph

variable (X : Graph) (G : Type) [Group G]

/-- Parallel transport of a connection `A` along one step. -/
def stepHol (A : Fin X.nE → G) (s : X.Step) : G := if s.2 then A s.1 else (A s.1)⁻¹

/-- Holonomy (ordered product of parallel transports) of `A` along a list of steps. -/
def hol (A : Fin X.nE → G) (w : List X.Step) : G := (w.map (stepHol X G A)).prod

/-- Gauge transformation `g : V → G` acting on a connection:
`(g • A) e = g (src e) * A e * (g (tgt e))⁻¹`. -/
def gaugeAct (g : Fin X.nV → G) (A : Fin X.nE → G) : Fin X.nE → G :=
  fun e => g (X.src e) * A e * (g (X.tgt e))⁻¹

variable {X G}

theorem hol_append (A : Fin X.nE → G) (w w' : List X.Step) :
    hol X G A (w ++ w') = hol X G A w * hol X G A w' := by
  simp [hol, List.map_append, List.prod_append]

theorem hol_backtrack (A : Fin X.nE → G) (p q : List X.Step) (s : X.Step) :
    hol X G A (p ++ s :: X.flip s :: q) = hol X G A (p ++ q) := by
  rcases s with ⟨e, b⟩
  cases b <;> simp [hol, stepHol, Graph.flip]

theorem gaugeAct_one (A : Fin X.nE → G) : gaugeAct X G 1 A = A := by
  funext e; simp [gaugeAct]

theorem gaugeAct_mul (g k : Fin X.nV → G) (A : Fin X.nE → G) :
    gaugeAct X G (k * g) A = gaugeAct X G k (gaugeAct X G g A) := by
  funext e; simp [gaugeAct, mul_assoc]

/-- Gauge covariance of holonomy along a walk from `x` to `y`. -/
theorem hol_gaugeAct (g : Fin X.nV → G) (A : Fin X.nE → G) :
    ∀ (w : List X.Step) (x y : Fin X.nV), X.IsPath x w y →
      hol X G (gaugeAct X G g A) w = g x * hol X G A w * (g y)⁻¹
  | [], x, y, h => by
      simp only [Graph.IsPath] at h; subst h; simp [hol]
  | s :: w, x, y, h => by
      obtain ⟨hs, hw⟩ := h
      have ih := hol_gaugeAct g A w _ y hw
      have hstep : stepHol X G (gaugeAct X G g A) s
          = g x * stepHol X G A s * (g (X.stepTgt s))⁻¹ := by
        subst hs
        rcases s with ⟨e, b⟩
        cases b <;> simp [stepHol, gaugeAct, Graph.stepSrc, Graph.stepTgt, mul_assoc]
      have h1 : hol X G (gaugeAct X G g A) (s :: w)
          = stepHol X G (gaugeAct X G g A) s * hol X G (gaugeAct X G g A) w := by
        simp [hol]
      have h2 : hol X G A (s :: w) = stepHol X G A s * hol X G A w := by simp [hol]
      rw [h1, h2, hstep, ih]; group

variable (X G)

/-! ### The groupoid of connections with gauge arrows -/

/-- Objects: `G`-connections on `X`. -/
structure PotG where
  conn : Fin X.nE → G

/-- Arrows `A ⟶ B`: gauge transformations `g` with `g • A = B`. -/
instance : Category (PotG X G) where
  Hom A B := {g : Fin X.nV → G // gaugeAct X G g A.conn = B.conn}
  id A := ⟨1, gaugeAct_one _⟩
  comp f k := ⟨k.1 * f.1, by rw [gaugeAct_mul, f.2, k.2]⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f k l := Subtype.ext (mul_assoc _ _ _).symm

/-! ### Holonomy maps at a base vertex -/

/-- A generalized holonomy map at the base vertex `x`: an assignment of group elements to
walks that is multiplicative on loops at `x` and unchanged by inserting a backtrack
`s, flip s` into a loop at `x`. Only its values on loops at `x` matter. -/
structure HolMap (x : Fin X.nV) where
  toFun : List X.Step → G
  mul : ∀ γ δ, X.IsPath x γ x → X.IsPath x δ x → toFun (γ ++ δ) = toFun γ * toFun δ
  backtrack : ∀ (p q : List X.Step) (s : X.Step) (y : Fin X.nV),
    X.IsPath x p y → X.stepSrc s = y → X.IsPath y q x →
      toFun (p ++ s :: X.flip s :: q) = toFun (p ++ q)

/-- Arrows `H ⟶ H'` of holonomy maps: `h : G` with `H' γ = h * H γ * h⁻¹` on every loop at `x`. -/
instance (x : Fin X.nV) : Category (HolMap X G x) where
  Hom H H' := {h : G // ∀ γ, X.IsPath x γ x → H'.toFun γ = h * H.toFun γ * h⁻¹}
  id H := ⟨1, fun γ _ => by simp⟩
  comp f k := ⟨k.1 * f.1, fun γ hγ => by rw [k.2 γ hγ, f.2 γ hγ]; group⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f k l := Subtype.ext (mul_assoc _ _ _).symm

/-- The holonomy map of a connection at `x`. -/
def holMapOf (x : Fin X.nV) (A : Fin X.nE → G) : HolMap X G x where
  toFun := hol X G A
  mul γ δ _ _ := hol_append A γ δ
  backtrack p q s _ _ _ _ := hol_backtrack A p q s

/-- The holonomy functor `A ↦ hol A`, `g ↦ g x`. -/
def holF (x : Fin X.nV) : PotG X G ⥤ HolMap X G x where
  obj A := holMapOf X G x A.conn
  map {A B} g := ⟨g.1 x, fun γ hγ => by
    have h := hol_gaugeAct (X := X) (G := G) g.1 A.conn γ x x hγ
    rw [show gaugeAct X G g.1 A.conn = B.conn from g.2] at h
    exact h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ### Gauge orbits and curvature -/

/-- Gauge equivalence of connections. -/
def gaugeSetoid : Setoid (Fin X.nE → G) where
  r A B := ∃ g, gaugeAct X G g A = B
  iseqv := ⟨fun A => ⟨1, gaugeAct_one A⟩,
    fun ⟨g, h⟩ => ⟨g⁻¹, by rw [← h, ← gaugeAct_mul, inv_mul_cancel, gaugeAct_one]⟩,
    fun ⟨g, h⟩ ⟨k, h'⟩ => ⟨k * g, by rw [gaugeAct_mul, h, h']⟩⟩

/-- The orbit functor: a connection goes to its gauge orbit, every arrow to an identity. -/
def orbitF : PotG X G ⥤ Discrete (Quotient (gaugeSetoid X G)) where
  obj A := Discrete.mk (Quotient.mk _ A.conn)
  map {A B} g := eqToHom (by
    congr 1; exact Quotient.sound ⟨g.1, g.2⟩)

/-- A finite 2-complex: a graph together with faces; face `f` has a base vertex and a
boundary walk `bd f`, a loop at `base f`. -/
structure Complex2 extends Graph where
  nF : ℕ
  base : Fin nF → Fin nV
  bd : Fin nF → List toGraph.Step
  bd_loop : ∀ f, toGraph.IsPath (base f) (bd f) (base f)

/-- The curvature (non-abelian field strength) functor on a 2-complex: a connection goes to
the family of conjugacy classes of its holonomies around the faces; arrows go to identities. -/
def curvF (Y : Complex2) : PotG Y.toGraph G ⥤ Discrete (Fin Y.nF → ConjClasses G) where
  obj A := Discrete.mk (fun f => ConjClasses.mk (hol Y.toGraph G A.conn (Y.bd f)))
  map {A B} g := eqToHom (by
    congr 1; funext f
    have h := hol_gaugeAct (X := Y.toGraph) (G := G) g.1 A.conn (Y.bd f) _ _ (Y.bd_loop f)
    rw [show gaugeAct Y.toGraph G g.1 A.conn = B.conn from g.2] at h
    rw [h, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    exact ⟨g.1 (Y.base f), rfl⟩)

/-! ### Example complexes -/

/-- The triangle graph: vertices `0,1,2`, edge `e` runs from `e` to `e + 1`. -/
abbrev triangle : Graph where
  nV := 3
  nE := 3
  src e := ⟨e.1, by omega⟩
  tgt e := ⟨(e.1 + 1) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The boundary of a triangle (a circle): the triangle graph with no faces. -/
def circleC : Complex2 where
  toGraph := triangle
  nF := 0
  base f := f.elim0
  bd f := f.elim0
  bd_loop f := f.elim0

/-- The filled triangle: the triangle graph with one face, based at `0`, whose boundary is
the loop `0 → 1 → 2 → 0`. -/
def filledC : Complex2 where
  toGraph := triangle
  nF := 1
  base _ := (0 : Fin 3)
  bd _ := [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)]
  bd_loop _ := by simp [Graph.IsPath, Graph.stepSrc, Graph.stepTgt]

end GaugeFunctor


