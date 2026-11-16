-- Prove2me | Definitions.Def_GuardedSSSP_Supplement_phaseOutput
-- name    : GuardedSSSP_Supplement_phaseOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:19:53.815791+00:00
-- url     : https://prove2.me/theorems/1d00198d-7f56-4ff0-94c6-76e070a4eec7
-- title:
--   Calibration, reduced costs, child quotients and the phase algorithm of Appendix E (output (54))
-- statement:
--   Fix a finite directed multigraph $H=(V,E)$ with weights $w\ge0$, a root $r$ reaching every vertex, a rooted tree $D$ on $V$ with root $r$, a child-before-parent order of $D$, and a seed vector $\beta\ge0$.
--
--   **Calibration (48)–(50).** $p(v)=\mathrm{dist}_H(r,v)$, $c(u,v)=p(u)+w(u,v)-p(v)$, $S=\max_v p(v)$. The initial intrinsic labels are $q(v)=\beta(v)+S-p(v)$ ($\infty$ for an absent seed), and the target is $z_\beta(v)=d_\beta(v)+S-p(v)$.
--
--   **Child quotient.** For a vertex $g$, $Q_g$ has one vertex per child of $g$. An arc $e=(u,v)$ whose tail lies in the subtree $D_a$ of a child $a$ and whose head is a different child $b$ is a **cross-sibling arc** and gives the quotient arc $a\to b$ of cost $c_e$. An arc $(u,g)$ with tail in $D_a$ for a child $a$ of $g$ is a **return arc** owned at $g$. The **residual** of an arc with tail $u\in D_a$ is
--
--   $$R_e=\min_{x\in D(a,u]}q(x),$$
--
--   the minimum over the tree path from $a$ to $u$ with $a$ excluded ($\infty$ if empty).
--
--   **Phase at $g$.** (1) The seed of each child $b$ is $\min\{q(b),\ \min_e(R_e+c_e)\}$ over cross-sibling arcs $e$ into $b$. (2) Every child cap $q(a)$ is replaced by $\min_b\big(\mathrm{seed}(b)+\mathrm{dist}_{Q_g}(b,a)\big)$. (3) $q(g)$ is replaced by $\min\{q(g),\ \min_e(\min\{q(a),R_e\}+c_e)\}$ over return arcs $e$ owned at $g$, with the step-2 value of $q(a)$. The phases are applied in the given order; then (54)
--
--   $$z(v)=\min_{x\in D[r,v]}q_{\mathrm{final}}(x).$$
--
--   This is the value-level algorithm whose exactness is Theorem E.3.
--
--   **Formalization Note** Labels are in `EReal` ($\top$ = absent); every empty minimum is $\top$. The calibration is `(dist G w r v).toReal`, used only under the hypothesis that $r$ reaches every vertex. The quotient distance is the infimum over walks of quotient arcs, the empty walk giving $0$. Step 4 (finishing the children) and the data structures of Appendices F and G change no value and are not modelled.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Appendix D, (48)–(50), p.38 (PDF p.39); Appendix E and E.1, (51)–(54), p.39 (PDF p.40)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist
import Definitions.Def_GuardedSSSP_Supplement_seededDist
import Definitions.Def_GuardedSSSP_Supplement_RootedTree

namespace GuardedSSSP

namespace Supplement

open AtomicDynRouting.ResidenceTime

/-!
# Calibration, reduced costs and the phase algorithm of Appendix E

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), Appendix D, (48)–(50), p.38 (PDF p.39), and Appendix E, E.1,
(51)–(54), p.39 (PDF p.40).

* (48): `p(v) = dist_H(r, v)`, `c(u, v) = p(u) + w(u, v) − p(v) ≥ 0`, `S = max_v p(v)`.
* (49): `q(v) = β(v) + S − p(v)`, absent if `β(v) = ∞`. (50): `z_β(v) = d_β(v) + S − p(v)`.
* Child quotient `Q_g`: one vertex per child of `g`; an arc `e = (u, v)` from the subtree of a child `a`
  to a different child root `v` gives the quotient arc `a → v` of cost `c_e` (parallel arcs kept). A return
  arc `(u, g)` is owned by its head; parent-to-child arcs and loops give no quotient arc.
* (52): the residual `R_e = min_{x ∈ D(a,u]} q(x)`, `∞` if empty or entirely absent.
* Phase `g`: (1) seed of each child `v` starts at `q(v)`; each cross-sibling arc `(u, v)` inserts
  `R_e + c_e`; (2) solve seeded shortest paths on `Q_g` with costs `c_e` and replace every child cap `q(a)`
  by the resulting quotient distance; (3) for each return `(u, g)` with `u ∈ D_a`, update `q(g)` by
  `min{q(a), R_e} + c_e`; (4) finish the children; (5) after the root, (54):
  `z(v) = min_{x ∈ D[r,v]} q_final(x)`.

**Formalization Note.**
* The phase algorithm is a function on values (labels in `EReal`, `⊤` = absent), not a RAM program;
  step 4 (finishing) changes no value. The vertices are processed in the order of positions of a
  bijection `ord : Fin n ≃ Fin n` (position `0` first); the theorem quantifies over every
  child-before-parent `ord`.
* The calibration is exact: `calib G w r v = (dist G w r v).toReal`. Every theorem that uses it assumes
  that `r` reaches every vertex (`dist G w r v ≠ ⊤`), so `toReal` is never applied to `⊤`.
* `S` is the maximum of `calib` over the nonempty vertex set (`r` is a vertex).
* A cross-sibling arc at `g` from child `a` to child `b ≠ a` is an arc whose tail lies in `D_a` and whose
  head is `b`. A return arc at `g` from child `a` is an arc whose tail lies in `D_a` and whose head is `g`.
  Parent-to-child arcs and loops satisfy neither condition, so they contribute nothing, as in the paper.
* The quotient distance `dist_{Q_g}(b, a)` is the infimum over quotient walks (lists of cross-sibling arcs
  at `g`, consecutive in `Q_g`) of the total reduced cost; the empty walk gives `dist_{Q_g}(a, a) = 0`.
* All infima are in `EReal`: an empty infimum is `⊤`, which is the paper's "∞ if empty or entirely absent".
* In step 3 the residual is evaluated on the labels after step 2; it involves only proper descendants of
  the children of `g`, which step 2 does not change, so it equals the step-1 residual.
-/

/-- The exact calibration `p(v) = dist_H(r, v)` (48), as a real number. -/
noncomputable def calib {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (r v : Fin n) : ℝ :=
  (dist G w r v).toReal

/-- `S = max_v p(v)` (48). -/
noncomputable def calibMax {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (r : Fin n) : ℝ :=
  Finset.univ.sup' ⟨r, Finset.mem_univ r⟩ (calib G w r)

/-- The reduced cost `c_e = p(u) + w_e − p(v)` of the arc `e = (u, v)` (48). -/
noncomputable def redCost {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (r : Fin n)
    (e : Fin m) : ℝ :=
  calib G w r (G.tail e) + w e - calib G w r (G.head e)

/-- The initial intrinsic label `q(v) = β(v) + S − p(v)` (49); `⊤` when the seed is absent. -/
noncomputable def initLabel {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (r : Fin n)
    (β : Fin n → EReal) (v : Fin n) : EReal :=
  β v + ((calibMax G w r - calib G w r v : ℝ) : EReal)

/-- The answer in reduced coordinates, `z_β(v) = d_β(v) + S − p(v)` (50). -/
noncomputable def zTarget {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (r : Fin n)
    (β : Fin n → EReal) (v : Fin n) : EReal :=
  seededDist G w β v + ((calibMax G w r - calib G w r v : ℝ) : EReal)

/-- The residual (52) `R = min_{x ∈ D(a,u]} q(x)`: the minimum of `q` over the tree path from `a` to `u`
with `a` excluded; `⊤` when that path is empty. -/
noncomputable def residual {n : ℕ} (par : Fin n → Fin n) (q : Fin n → EReal) (a u : Fin n) : EReal :=
  ⨅ (x : Fin n) (_ : IsAnc par a x ∧ IsAnc par x u ∧ x ≠ a), q x

/-- `e` is a cross-sibling arc owned at `g`, from the subtree of the child `a` to the different child
root `b`; it gives the quotient arc `a → b` of `Q_g`. -/
def IsCrossArc {n m : ℕ} (G : Network (Fin n) (Fin m)) (par : Fin n → Fin n) (r g a b : Fin n)
    (e : Fin m) : Prop :=
  IsChild par r g a ∧ IsChild par r g b ∧ a ≠ b ∧ IsAnc par a (G.tail e) ∧ G.head e = b

/-- `e` is a return arc owned at its head `g`, with tail in the subtree of the child `a` of `g`. -/
def IsReturnArc {n m : ℕ} (G : Network (Fin n) (Fin m)) (par : Fin n → Fin n) (r g a : Fin n)
    (e : Fin m) : Prop :=
  IsChild par r g a ∧ IsAnc par a (G.tail e) ∧ G.head e = g

/-- `P` is a walk in the child quotient `Q_g` from the child `b` to the child `a`: a list of quotient
arcs, each starting at the child where the previous one ended. -/
def IsQuotientWalk {n m : ℕ} (G : Network (Fin n) (Fin m)) (par : Fin n → Fin n) (r g : Fin n) :
    Fin n → Fin n → List (Fin m) → Prop
  | b, a, [] => b = a
  | b, a, e :: P => IsCrossArc G par r g b (G.head e) e ∧ IsQuotientWalk G par r g (G.head e) a P

open Classical in
/-- One phase of the algorithm at the tree vertex `g` (steps 1–3 of E.1), acting on the label vector
`q`. Step 1 builds the quotient seeds, step 2 replaces every child cap by its seeded quotient distance,
step 3 applies the return updates to `q(g)`. -/
noncomputable def phase {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ)
    (par : Fin n → Fin n) (r g : Fin n) (q : Fin n → EReal) : Fin n → EReal :=
  let c : Fin m → ℝ := redCost G w r
  -- step 1: quotient seeds
  let seed : Fin n → EReal := fun b =>
    min (q b) (⨅ (a : Fin n) (e : Fin m) (_ : IsCrossArc G par r g a b e),
      residual par q a (G.tail e) + ((c e : ℝ) : EReal))
  -- step 2: every child cap becomes its seeded quotient distance
  let q2 : Fin n → EReal := fun v =>
    if IsChild par r g v then
      ⨅ (b : Fin n) (_ : IsChild par r g b) (P : List (Fin m)) (_ : IsQuotientWalk G par r g b v P),
        seed b + (((P.map c).sum : ℝ) : EReal)
    else q v
  -- step 3: return updates of q(g), using the step-2 caps
  fun v =>
    if v = g then
      min (q2 g) (⨅ (a : Fin n) (e : Fin m) (_ : IsReturnArc G par r g a e),
        min (q2 a) (residual par q2 a (G.tail e)) + ((c e : ℝ) : EReal))
    else q2 v

/-- The final intrinsic labels `q_final`: the phases applied to the initial labels (49) in the order of
the positions of `ord` (position `0` first). -/
noncomputable def finalLabels {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ)
    (par : Fin n → Fin n) (r : Fin n) (ord : Fin n ≃ Fin n) (β : Fin n → EReal) : Fin n → EReal :=
  (List.finRange n).foldl (fun q i => phase G w par r (ord.symm i) q) (initLabel G w r β)

/-- The output (54) of the phase algorithm: `z(v) = min_{x ∈ D[r,v]} q_final(x)`, the minimum of the
final labels over the ancestors of `v` (inclusive). -/
noncomputable def phaseOutput {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ)
    (par : Fin n → Fin n) (r : Fin n) (ord : Fin n ≃ Fin n) (β : Fin n → EReal) (v : Fin n) :
    EReal :=
  ⨅ (x : Fin n) (_ : IsAnc par x v), finalLabels G w par r ord β x

end Supplement

end GuardedSSSP


