-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus
-- name    : liuyao_ca_fd889115_k1_Analysis_Calculus
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:51:19.836408+00:00
-- url     : https://prove2.me/theorems/0645955e-4989-47e4-a213-a9fb229c9e95
-- title:
--   Computable analysis · Calculus · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/Calculus.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

namespace ComputableAnalysis

def mesh (a b : Rat) (n : Nat) : Rat := if n = 0 then 0 else (b - a) / n
def leftPoint (a b : Rat) (n k : Nat) : Rat := a + (k : Rat) * mesh a b n

/-- The first point of every positive uniform rational mesh is its left
endpoint. -/
theorem leftPoint_zero (a b : Rat) (n : Nat) :
    leftPoint a b n 0 = a := by
  unfold leftPoint
  grind

/-! Doubling the public half-interval identifies its equal-mesh sample grid
with the normalized unit-interval grid. -/
theorem two_mul_leftPoint_zero_half_eq_leftPoint_zero_one
    (n k : Nat) :
    2 * leftPoint 0 ((1 : Rat) / 2) n k = leftPoint 0 1 n k := by
  by_cases hn : n = 0
  · subst n
    simp [leftPoint, mesh]
    decide +kernel
  · have hnrat : (n : Rat) ≠ 0 := by
      exact Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn))
    unfold leftPoint mesh
    rw [if_neg hn, if_neg hn]
    simp only [Rat.zero_add]
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel _ hnrat]

theorem mesh_zero_half_eq_half_mesh_zero_one (n : Nat) :
    mesh 0 ((1 : Rat) / 2) n = (1 / 2) * mesh 0 1 n := by
  by_cases hn : n = 0
  · subst n
    simp [mesh]
  · have hnr : (n : Rat) ≠ 0 :=
      Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn))
    unfold mesh
    rw [if_neg hn, if_neg hn, Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hnr]

/-- The last point of a positive uniform rational mesh is its right endpoint.
This is an exact rational identity; no limiting argument is involved. -/
theorem leftPoint_endpoint {a b : Rat} {n : Nat} (hn : 0 < n) :
    leftPoint a b n n = b := by
  have hnat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  unfold leftPoint mesh
  rw [if_neg (Nat.ne_of_gt hn)]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
    Rat.sub_eq_add_neg]

/-- Consecutive points of a uniform rational mesh are separated by precisely
its mesh width. -/
theorem leftPoint_step (a b : Rat) (n k : Nat) :
    leftPoint a b n (k + 1) - leftPoint a b n k = mesh a b n := by
  unfold leftPoint
  grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add, Rat.add_assoc,
    Rat.add_comm]

/-- The mesh width is nonnegative on an ordered interval. -/
theorem mesh_nonneg_of_le {a b : Rat} {n : Nat}
    (hn : 0 < n) (hab : a <= b) :
    0 <= mesh a b n := by
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hn), Rat.div_def]
  have hden : 0 <= ((n : Rat)⁻¹) :=
    Rat.le_of_lt (Rat.inv_pos.mpr ((Rat.natCast_pos).2 hn))
  exact Rat.mul_nonneg (by grind [Rat.sub_eq_add_neg]) hden

/-- The total width of a positive uniform mesh is exactly the interval width.
This is the finite algebraic normalization behind replacing a common value
range budget by a global rectangle-gap budget. -/
theorem natCast_mul_mesh_eq_sub {a b : Rat} {n : Nat} (hn : 0 < n) :
    (n : Rat) * mesh a b n = b - a := by
  have hnat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hn), Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- An ordered interval gives an ordered uniform rational mesh. -/
theorem leftPoint_monotone {a b : Rat} {n i j : Nat}
    (hn : 0 < n) (hab : a <= b) (hij : i <= j) :
    leftPoint a b n i <= leftPoint a b n j := by
  have hmesh : 0 <= mesh a b n := mesh_nonneg_of_le hn hab
  have hcast : (i : Rat) <= (j : Rat) := by
    exact_mod_cast hij
  exact (Rat.add_le_add_left).mpr
    (Rat.mul_le_mul_of_nonneg_right hcast hmesh)

/-- Refining a uniform mesh by a positive factor preserves every old mesh
point.  The embedding sends index `i` to `i*n` in the `m*n` mesh. -/
theorem leftPoint_refine_mul_right {a b : Rat} {m n i : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    leftPoint a b (m * n) (i * n) = leftPoint a b m i := by
  have hmrat : (m : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hm)
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  unfold leftPoint mesh
  rw [if_neg (Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)),
    if_neg (Nat.ne_of_gt hm)]
  simp only [Rat.natCast_mul]
  grind [Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

/-- Under the same refinement, the fine mesh width is the old width divided
by the positive refinement factor. -/
theorem mesh_refine_mul_right {a b : Rat} {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    mesh a b (m * n) = mesh a b m / (n : Rat) := by
  unfold mesh
  rw [if_neg (Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)),
    if_neg (Nat.ne_of_gt hm)]
  simp only [Rat.natCast_mul]
  grind [Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

/-- Successive dyadic meshes preserve every previous grid point.  The old
index `k` is the new index `2*k`; this is the exact finite compatibility
behind stagewise dyadic Riemann constructions. -/
theorem dyadic_leftPoint_refines (a b : Rat) (n k : Nat) :
    leftPoint a b (2 ^ (n + 1)) (2 * k) =
      leftPoint a b (2 ^ n) k := by
  have hpow : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have htwo : 0 < 2 := by omega
  simpa [Nat.pow_succ, Nat.mul_comm] using
    leftPoint_refine_mul_right (a := a) (b := b) (i := k) hpow htwo

/-- The dyadic mesh width is halved at every successor stage. -/
theorem dyadic_mesh_refines (a b : Rat) (n : Nat) :
    mesh a b (2 ^ (n + 1)) = mesh a b (2 ^ n) / 2 := by
  have hpow : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have htwo : 0 < 2 := by omega
  simpa [Nat.pow_succ] using mesh_refine_mul_right
    (a := a) (b := b) hpow htwo

def riemannLeftExact (g : Rat -> Rat) (a b : Rat) (n : Nat) : Rat :=
  let h := mesh a b n
  (List.range n).foldl (fun acc k => acc + h * g (leftPoint a b n k)) 0

def riemannLeftInterval (g : RealFunRaw) (a b : Rat) (n : Nat) (prec : Nat) : QInterval :=
  let h := mesh a b n
  (List.range n).foldl
    (fun acc k => let I := g.compute (leftPoint a b n k) prec; { lo := acc.lo + h * I.lo, hi := acc.hi + h * I.hi })
    { lo := 0, hi := 0 }

/-! Right-endpoint rectangles use the same rational mesh and interval
arithmetic, changing only the sampled point from `k` to `k + 1`.  Keeping
this as a separate finite construction makes the choice of Riemann convention
visible without appealing to a limiting equivalence. -/

def rightPoint (a b : Rat) (n k : Nat) : Rat :=
  leftPoint a b n (k + 1)

def riemannRightInterval (g : RealFunRaw) (a b : Rat) (n : Nat) (prec : Nat) : QInterval :=
  let h := mesh a b n
  (List.range n).foldl
    (fun acc k => let I := g.compute (rightPoint a b n k) prec; { lo := acc.lo + h * I.lo, hi := acc.hi + h * I.hi })
    { lo := 0, hi := 0 }

/-! The finite trapezoid schedule averages the two endpoint boxes on each
cell.  It is a third presentation of the same rational rectangle data; no
limit or completeness principle is part of its definition. -/

def riemannTrapezoidInterval (g : RealFunRaw) (a b : Rat) (n : Nat) (prec : Nat) : QInterval :=
  let h := mesh a b n
  (List.range n).foldl
    (fun acc k =>
      let L := g.compute (leftPoint a b n k) prec
      let R := g.compute (rightPoint a b n k) prec
      { lo := acc.lo + (h / 2) * (L.lo + R.lo),
        hi := acc.hi + (h / 2) * (L.hi + R.hi) })
    { lo := 0, hi := 0 }

/-- The finite rectangle sum is insensitive to how an evaluator behaves away
from its sample points.  This is the bridge used by the computable sine
integral: a specialized nested-radical evaluator only needs to agree with
the public `sin (pi*x)` evaluator on the dyadic left endpoints actually read
by the equal-mesh algorithm. -/
theorem riemannLeftInterval_congr_of_samples
    (g h : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall k, k < subdivisions ->
      g.compute (leftPoint a b subdivisions k) prec =
        h.compute (leftPoint a b subdivisions k) prec) :
    riemannLeftInterval g a b subdivisions prec =
      riemannLeftInterval h a b subdivisions prec := by
  unfold riemannLeftInterval
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < subdivisions) ->
      forall (acc : QInterval),
      (xs.foldl
        (fun acc k =>
          let I := g.compute (leftPoint a b subdivisions k) prec
          { lo := acc.lo + mesh a b subdivisions * I.lo,
            hi := acc.hi + mesh a b subdivisions * I.hi }) acc) =
      (xs.foldl
        (fun acc k =>
          let I := h.compute (leftPoint a b subdivisions k) prec
          { lo := acc.lo + mesh a b subdivisions * I.lo,
            hi := acc.hi + mesh a b subdivisions * I.hi }) acc) := by
    intro xs
    induction xs with
    | nil =>
        intro _hmem
        intro acc
        rfl
    | cons k ks ih =>
        intro hmem
        intro acc
        dsimp
        rw [hpoint k (hmem k (by simp))]
        exact ih (fun j hj => hmem j (by simp [hj])) _
  exact hfold (List.range subdivisions)
    (by intro k hk; exact List.mem_range.mp hk) { lo := 0, hi := 0 }

/-- Overlapping sample boxes give overlapping rectangle sums.

This is the interval-valued version of the sample-transport lemma above.  It
is intentionally weaker than exact sample equality: a specialized evaluator
may use nested radicals, Taylor bounds, or another finite algorithm, provided
that its box at every sampled dyadic point overlaps the public evaluator's
box.  The proof is finite induction over the mesh; the only order fact used
is that the mesh width is nonnegative. -/
theorem riemannLeftInterval_overlap_of_samples
    (g h : RealFunRaw) (a b : Rat) (hab : a <= b)
    (subdivisions prec : Nat)
    (hpoint : forall k, k < subdivisions ->
      QInterval.Overlaps
        (g.compute (leftPoint a b subdivisions k) prec)
        (h.compute (leftPoint a b subdivisions k) prec)) :
    QInterval.Overlaps
      (riemannLeftInterval g a b subdivisions prec)
      (riemannLeftInterval h a b subdivisions prec) := by
  unfold riemannLeftInterval
  have hmesh : 0 <= mesh a b subdivisions := by
    by_cases hn : 0 < subdivisions
    · exact mesh_nonneg_of_le hn hab
    · have hz : subdivisions = 0 := by omega
      simp [mesh, hz]
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < subdivisions) ->
      forall (accG accH : QInterval), QInterval.Overlaps accG accH ->
      QInterval.Overlaps
        (xs.foldl
          (fun acc k =>
            let I := g.compute (leftPoint a b subdivisions k) prec
            { lo := acc.lo + mesh a b subdivisions * I.lo,
              hi := acc.hi + mesh a b subdivisions * I.hi })
          accG)
        (xs.foldl
          (fun acc k =>
            let I := h.compute (leftPoint a b subdivisions k) prec
            { lo := acc.lo + mesh a b subdivisions * I.lo,
              hi := acc.hi + mesh a b subdivisions * I.hi })
          accH) := by
    intro xs
    induction xs with
    | nil =>
        intro _ accG accH hover
        exact hover
    | cons k ks ih =>
        intro hmem
        have hk : k < subdivisions := hmem k (by simp)
        have hks : forall j, j ∈ ks -> j < subdivisions := by
          intro j hj
          exact hmem j (by simp [hj])
        intro accG accH hover
        have hsample := hpoint k hk
        have hstep : QInterval.Overlaps
            { lo := accG.lo + mesh a b subdivisions *
                (g.compute (leftPoint a b subdivisions k) prec).lo,
              hi := accG.hi + mesh a b subdivisions *
                (g.compute (leftPoint a b subdivisions k) prec).hi }
            { lo := accH.lo + mesh a b subdivisions *
                (h.compute (leftPoint a b subdivisions k) prec).lo,
              hi := accH.hi + mesh a b subdivisions *
                (h.compute (leftPoint a b subdivisions k) prec).hi } := by
          unfold QInterval.Overlaps at hover hsample ⊢
          constructor
          · have hscaled :
              mesh a b subdivisions *
                  (g.compute (leftPoint a b subdivisions k) prec).lo <=
                mesh a b subdivisions *
                  (h.compute (leftPoint a b subdivisions k) prec).hi :=
            Rat.mul_le_mul_of_nonneg_left hsample.1 hmesh
            grind
          · have hscaled :
              mesh a b subdivisions *
                  (h.compute (leftPoint a b subdivisions k) prec).lo <=
                mesh a b subdivisions *
                  (g.compute (leftPoint a b subdivisions k) prec).hi :=
            Rat.mul_le_mul_of_nonneg_left hsample.2 hmesh
            grind
        simpa using ih hks _ _ hstep
  exact hfold (List.range subdivisions)
    (by intro k hk; exact List.mem_range.mp hk)
    { lo := 0, hi := 0 } { lo := 0, hi := 0 } (by
      simp [QInterval.Overlaps])

/-- Right-endpoint rectangle sums have the same exact sample-transport law.
The proof is again only a finite fold induction; no relation between left and
right limits is assumed. -/
theorem riemannRightInterval_congr_of_samples
    (g h : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall k, k < subdivisions ->
      g.compute (rightPoint a b subdivisions k) prec =
        h.compute (rightPoint a b subdivisions k) prec) :
    riemannRightInterval g a b subdivisions prec =
      riemannRightInterval h a b subdivisions prec := by
  unfold riemannRightInterval
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < subdivisions) ->
      forall (acc : QInterval),
      (xs.foldl
        (fun acc k =>
          let I := g.compute (rightPoint a b subdivisions k) prec
          { lo := acc.lo + mesh a b subdivisions * I.lo,
            hi := acc.hi + mesh a b subdivisions * I.hi }) acc) =
      (xs.foldl
        (fun acc k =>
          let I := h.compute (rightPoint a b subdivisions k) prec
          { lo := acc.lo + mesh a b subdivisions * I.lo,
            hi := acc.hi + mesh a b subdivisions * I.hi }) acc) := by
    intro xs
    induction xs with
    | nil =>
        intro _hmem
        intro acc
        rfl
    | cons k ks ih =>
        intro hmem
        intro acc
        dsimp
        rw [hpoint k (hmem k (by simp))]
        exact ih (fun j hj => hmem j (by simp [hj])) _
  exact hfold (List.range subdivisions)
    (by intro k hk; exact List.mem_range.mp hk) { lo := 0, hi := 0 }

/-- Overlapping right-endpoint sample boxes propagate to overlapping right
rectangle sums.  The ordered-interval hypothesis is used only to preserve
overlap under multiplication by the mesh width. -/
theorem riemannRightInterval_overlap_of_samples
    (g h : RealFunRaw) (a b : Rat) (hab : a <= b)
    (subdivisions prec : Nat)
    (hpoint : forall k, k < subdivisions ->
      QInterval.Overlaps
        (g.compute (rightPoint a b subdivisions k) prec)
        (h.compute (rightPoint a b subdivisions k) prec)) :
    QInterval.Overlaps
      (riemannRightInterval g a b subdivisions prec)
      (riemannRightInterval h a b subdivisions prec) := by
  unfold riemannRightInterval
  have hmesh : 0 <= mesh a b subdivisions := by
    by_cases hn : 0 < subdivisions
    · exact mesh_nonneg_of_le hn hab
    · have hz : subdivisions = 0 := by omega
      simp [mesh, hz]
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < subdivisions) ->
      forall (accG accH : QInterval), QInterval.Overlaps accG accH ->
      QInterval.Overlaps
        (xs.foldl
          (fun acc k =>
            let I := g.compute (rightPoint a b subdivisions k) prec
            { lo := acc.lo + mesh a b subdivisions * I.lo,
              hi := acc.hi + mesh a b subdivisions * I.hi })
          accG)
        (xs.foldl
          (fun acc k =>
            let I := h.compute (rightPoint a b subdivisions k) prec
            { lo := acc.lo + mesh a b subdivisions * I.lo,
              hi := acc.hi + mesh a b subdivisions * I.hi })
          accH) := by
    intro xs
    induction xs with
    | nil =>
        intro _ accG accH hover
        exact hover
    | cons k ks ih =>
        intro hmem
        have hk : k < subdivisions := hmem k (by simp)
        have hks : forall j, j ∈ ks -> j < subdivisions := by
          intro j hj
          exact hmem j (by simp [hj])
        intro accG accH hover
        have hsample := hpoint k hk
        have hstep : QInterval.Overlaps
            { lo := accG.lo + mesh a b subdivisions *
                (g.compute (rightPoint a b subdivisions k) prec).lo,
              hi := accG.hi + mesh a b subdivisions *
                (g.compute (rightPoint a b subdivisions k) prec).hi }
            { lo := accH.lo + mesh a b subdivisions *
                (h.compute (rightPoint a b subdivisions k) prec).lo,
              hi := accH.hi + mesh a b subdivisions *
                (h.compute (rightPoint a b subdivisions k) prec).hi } := by
          unfold QInterval.Overlaps at hover hsample ⊢
          constructor
          · have hscaled :
              mesh a b subdivisions *
                  (g.compute (rightPoint a b subdivisions k) prec).lo <=
                mesh a b subdivisions *
                  (h.compute (rightPoint a b subdivisions k) prec).hi :=
            Rat.mul_le_mul_of_nonneg_left hsample.1 hmesh
            grind
          · have hscaled :
              mesh a b subdivisions *
                  (h.compute (rightPoint a b subdivisions k) prec).lo <=
                mesh a b subdivisions *
                  (g.compute (rightPoint a b subdivisions k) prec).hi :=
            Rat.mul_le_mul_of_nonneg_left hsample.2 hmesh
            grind
        simpa using ih hks _ _ hstep
  exact hfold (List.range subdivisions)
    (by intro k hk; exact List.mem_range.mp hk)
    { lo := 0, hi := 0 } { lo := 0, hi := 0 } (by
      simp [QInterval.Overlaps])

/-- The finite left-endpoint sum for the product contribution
`f\,\Delta g`.  This is the rational rectangle area swept when the second
side of a rectangle changes while the first is held at its left endpoint. -/
def leftStieltjesSum (f g : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => leftStieltjesSum f g n + f n * (g (n + 1) - g n)

/-- The recursive Stieltjes sum is literally the finite fold over its cell
indices.  This form is convenient when a substitution re-enumerates the same
finite cells. -/
theorem leftStieltjesSum_eq_range_fold (f g : Nat -> Rat) (n : Nat) :
    leftStieltjesSum f g n =
      (List.range n).foldl
        (fun acc k => acc + f k * (g (k + 1) - g k)) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [leftStieltjesSum, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]

/-- Pointwise equality on a finite index list transports through a rational
addition fold. -/
theorem rat_add_fold_congr_on (xs : List Nat) (left right : Nat -> Rat)
    (hterm : forall k, k ∈ xs -> left k = right k) (initial : Rat) :
    xs.foldl (fun acc k => acc + left k) initial =
      xs.foldl (fun acc k => acc + right k) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons k xs ih =>
      simp only [List.foldl]
      rw [hterm k (by simp)]
      apply ih
      intro j hj
      exact hterm j (List.mem_cons_of_mem k hj)

/-- The complementary finite right-endpoint sum `g_{i+1}\,\Delta f_i`.
Together with `leftStieltjesSum` it fills the endpoint-product rectangle
exactly, before any limiting argument is made. -/
def rightStieltjesSum (f g : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => rightStieltjesSum f g n + g (n + 1) * (f (n + 1) - f n)

/-- The finite corner-rectangle correction obtained if both Stieltjes sums
use left endpoints.  A constructive integration-by-parts proof only has to
show this displayed rational sum tends to zero on its chosen mesh. -/
def quadraticVariationSum (f g : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => quadraticVariationSum f g n +
      (f (n + 1) - f n) * (g (n + 1) - g n)

/-! The finite linearity laws for Stieltjes sums.  These expose the algebra
used by substitution and termwise integration without introducing a limiting
integral or a completed real. -/

theorem leftStieltjesSum_add_left (f h g : Nat -> Rat) (n : Nat) :
    leftStieltjesSum (fun i => f i + h i) g n =
      leftStieltjesSum f g n + leftStieltjesSum h g n := by
  induction n with
  | zero =>
      change 0 = 0 + 0
      exact (Rat.add_zero 0).symm
  | succ n ih =>
      rw [leftStieltjesSum, leftStieltjesSum, leftStieltjesSum, ih]
      grind [Rat.add_mul, Rat.add_assoc, Rat.add_comm]

theorem leftStieltjesSum_add_right (f g h : Nat -> Rat) (n : Nat) :
    leftStieltjesSum f (fun i => g i + h i) n =
      leftStieltjesSum f g n + leftStieltjesSum f h n := by
  induction n with
  | zero =>
      change 0 = 0 + 0
      exact (Rat.add_zero 0).symm
  | succ n ih =>
      rw [leftStieltjesSum, leftStieltjesSum, leftStieltjesSum, ih]
      grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem rightStieltjesSum_add_left (f h g : Nat -> Rat) (n : Nat) :
    rightStieltjesSum (fun i => f i + h i) g n =
      rightStieltjesSum f g n + rightStieltjesSum h g n := by
  induction n with
  | zero =>
      change 0 = 0 + 0
      exact (Rat.add_zero 0).symm
  | succ n ih =>
      rw [rightStieltjesSum, rightStieltjesSum, rightStieltjesSum, ih]
      grind [Rat.add_mul, Rat.add_assoc, Rat.add_comm]

theorem rightStieltjesSum_add_right (f g h : Nat -> Rat) (n : Nat) :
    rightStieltjesSum f (fun i => g i + h i) n =
      rightStieltjesSum f g n + rightStieltjesSum f h n := by
  induction n with
  | zero =>
      change 0 = 0 + 0
      exact (Rat.add_zero 0).symm
  | succ n ih =>
      rw [rightStieltjesSum, rightStieltjesSum, rightStieltjesSum, ih]
      grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem leftStieltjesSum_scale_left (c : Rat) (f g : Nat -> Rat) (n : Nat) :
    leftStieltjesSum (fun i => c * f i) g n =
      c * leftStieltjesSum f g n := by
  induction n with
  | zero =>
      change 0 = c * 0
      simp
  | succ n ih =>
      rw [leftStieltjesSum, ih]
      calc
        c * leftStieltjesSum f g n +
              (c * f n) * (g (n + 1) - g n) =
            c * leftStieltjesSum f g n +
              c * (f n * (g (n + 1) - g n)) := by
                rw [Rat.mul_assoc]
        _ = c * (leftStieltjesSum f g n +
              f n * (g (n + 1) - g n)) := by
                rw [Rat.mul_add]

theorem rightStieltjesSum_scale_left (c : Rat) (f g : Nat -> Rat) (n : Nat) :
    rightStieltjesSum (fun i => c * f i) g n =
      c * rightStieltjesSum f g n := by
  induction n with
  | zero =>
      change 0 = c * 0
      simp
  | succ n ih =>
      rw [rightStieltjesSum, ih]
      have hstep :
          c * f (n + 1) - c * f n =
            c * (f (n + 1) - f n) := by
        simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg]
      rw [hstep]
      calc
        c * rightStieltjesSum f g n +
              g (n + 1) * (c * (f (n + 1) - f n)) =
            c * rightStieltjesSum f g n +
              c * (g (n + 1) * (f (n + 1) - f n)) := by
                congr 1
                grind [Rat.mul_assoc, Rat.mul_comm]
        _ = c * (rightStieltjesSum f g n +
              g (n + 1) * (f (n + 1) - f n)) := by
                rw [Rat.mul_add]

theorem leftStieltjesSum_scale_right (c : Rat) (f g : Nat -> Rat) (n : Nat) :
    leftStieltjesSum f (fun i => c * g i) n =
      c * leftStieltjesSum f g n := by
  induction n with
  | zero =>
      change 0 = c * 0
      simp
  | succ n ih =>
      rw [leftStieltjesSum, ih]
      have hstep :
          c * g (n + 1) - c * g n =
            c * (g (n + 1) - g n) := by
        simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg]
      rw [hstep]
      calc
        c * leftStieltjesSum f g n +
              f n * (c * (g (n + 1) - g n)) =
            c * leftStieltjesSum f g n +
              c * (f n * (g (n + 1) - g n)) := by
                congr 1
                grind [Rat.mul_assoc, Rat.mul_comm]
        _ = c * (leftStieltjesSum f g n +
              f n * (g (n + 1) - g n)) := by
                rw [Rat.mul_add]

theorem rightStieltjesSum_scale_right (c : Rat) (f g : Nat -> Rat) (n : Nat) :
    rightStieltjesSum f (fun i => c * g i) n =
      c * rightStieltjesSum f g n := by
  induction n with
  | zero =>
      change 0 = c * 0
      simp
  | succ n ih =>
      rw [rightStieltjesSum, ih]
      calc
        c * rightStieltjesSum f g n +
              (c * g (n + 1)) * (f (n + 1) - f n) =
            c * rightStieltjesSum f g n +
              c * (g (n + 1) * (f (n + 1) - f n)) := by
                rw [Rat.mul_assoc]
        _ = c * (rightStieltjesSum f g n +
              g (n + 1) * (f (n + 1) - f n)) := by
                rw [Rat.mul_add]

/-- One cell of the geometric integration-by-parts decomposition: the two
oriented strips exactly make up the change in the endpoint-product rectangle. -/
theorem productIncrement_decomposition
    (f0 f1 g0 g1 : Rat) :
    f1 * g1 - f0 * g0 =
      f0 * (g1 - g0) + g1 * (f1 - f0) := by
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-! The corresponding finite product transport for rational secant slopes. -/

/-- A product secant is the endpoint-weighted sum of the two factor secants.

This is the exact rational, finite-difference analogue of the product rule:
the first factor is sampled at the left endpoint and the second at the right
endpoint.  The positivity hypothesis records that the quotient is taken over
an actual forward cell; no completed real or limiting argument is involved. -/
theorem secantSlope_product_transport
    {x y f0 f1 g0 g1 : Rat} (hxy : x < y) :
    (f1 * g1 - f0 * g0) / (y - x) =
      f0 * ((g1 - g0) / (y - x)) +
        g1 * ((f1 - f0) / (y - x)) := by
  have hden_pos : 0 < y - x := (Rat.lt_iff_sub_pos x y).mp hxy
  have hden : y - x ≠ 0 := Rat.ne_of_gt hden_pos
  have hden_inv : (y - x) * (y - x)⁻¹ = 1 :=
    Rat.mul_inv_cancel (y - x) hden
  rw [productIncrement_decomposition, Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.add_mul, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
    Rat.add_assoc, Rat.add_comm]

/-- Finite geometric integration by parts.  The two displayed sums tile the
rectangle difference `f_n g_n-f_0 g_0`; on a subdivision `t_i` these are the
samples `f(t_i)` and `g(t_i)`.  This is an exact rational identity, not a
statement about unrepresented limiting real numbers. -/
theorem finiteIntegrationByParts (f g : Nat -> Rat) (n : Nat) :
    leftStieltjesSum f g n + rightStieltjesSum f g n =
      f n * g n - f 0 * g 0 := by
  induction n with
  | zero =>
      grind [leftStieltjesSum, rightStieltjesSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [leftStieltjesSum, rightStieltjesSum]
      have hcell := productIncrement_decomposition
        (f n) (f (n + 1)) (g n) (g (n + 1))
      calc
        (leftStieltjesSum f g n + f n * (g (n + 1) - g n)) +
            (rightStieltjesSum f g n + g (n + 1) * (f (n + 1) - f n)) =
          (leftStieltjesSum f g n + rightStieltjesSum f g n) +
            (f n * (g (n + 1) - g n) +
              g (n + 1) * (f (n + 1) - f n)) := by
            grind [Rat.add_assoc, Rat.add_comm]
        _ = (f n * g n - f 0 * g 0) +
            (f n * (g (n + 1) - g n) +
              g (n + 1) * (f (n + 1) - f n)) := by rw [ih]
        _ = f (n + 1) * g (n + 1) - f 0 * g 0 := by
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
              Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The same rectangle decomposition when both sums use left endpoints.  The
only difference from the exact tiling is the explicitly named corner-area
sum `quadraticVariationSum`. -/
theorem finiteIntegrationByParts_withVariation
    (f g : Nat -> Rat) (n : Nat) :
    leftStieltjesSum f g n + leftStieltjesSum g f n +
        quadraticVariationSum f g n =
      f n * g n - f 0 * g 0 := by
  induction n with
  | zero =>
      grind [leftStieltjesSum, quadraticVariationSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [leftStieltjesSum, leftStieltjesSum, quadraticVariationSum]
      have hcell :
          f (n + 1) * g (n + 1) - f n * g n =
            f n * (g (n + 1) - g n) +
              g n * (f (n + 1) - f n) +
              (f (n + 1) - f n) * (g (n + 1) - g n) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      calc
        (leftStieltjesSum f g n + f n * (g (n + 1) - g n)) +
              (leftStieltjesSum g f n + g n * (f (n + 1) - f n)) +
            (quadraticVariationSum f g n +
              (f (n + 1) - f n) * (g (n + 1) - g n)) =
          (leftStieltjesSum f g n + leftStieltjesSum g f n +
              quadraticVariationSum f g n) +
            (f n * (g (n + 1) - g n) +
              g n * (f (n + 1) - f n) +
              (f (n + 1) - f n) * (g (n + 1) - g n)) := by
            grind [Rat.add_assoc, Rat.add_comm]
        _ = (f n * g n - f 0 * g 0) +
            (f n * (g (n + 1) - g n) +
              g n * (f (n + 1) - f n) +
              (f (n + 1) - f n) * (g (n + 1) - g n)) := by rw [ih]
        _ = f (n + 1) * g (n + 1) - f 0 * g 0 := by
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
              Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-! The square case is the finite chain rule.  It is the form used by
substitution and by energy estimates: the endpoint change of `f^2` is the
left-endpoint sum for `2 f df`, plus the explicitly visible quadratic
variation.  No limiting integral or completed real is involved. -/

theorem finiteSquareStieltjes_chain (f : Nat -> Rat) (n : Nat) :
    2 * leftStieltjesSum f f n + quadraticVariationSum f f n =
      f n * f n - f 0 * f 0 := by
  have h := finiteIntegrationByParts_withVariation f f n
  rw [show leftStieltjesSum f f n + leftStieltjesSum f f n =
      2 * leftStieltjesSum f f n by
        grind [Rat.add_comm, Rat.mul_comm]] at h
  exact h

/-! The chain rule immediately gives a finite error bracket for the
left-endpoint square sum.  This is the form used by an effective integral:
the quadratic variation is not discarded, but carried as the explicit error
budget `eps`. -/

theorem finiteSquareStieltjes_left_bounds
    (f : Nat -> Rat) (n : Nat) (eps : Rat)
    (hvariation : 0 <= quadraticVariationSum f f n)
    (hvariation_le : quadraticVariationSum f f n <= eps) :
    f n * f n - f 0 * f 0 - eps <=
        2 * leftStieltjesSum f f n /\
      2 * leftStieltjesSum f f n <=
        f n * f n - f 0 * f 0 := by
  have hchain := finiteSquareStieltjes_chain f n
  constructor <;> grind

theorem rightStieltjesSum_eq_left_swap_add_quadraticVariation
    (f g : Nat -> Rat) (n : Nat) :
    rightStieltjesSum f g n =
      leftStieltjesSum g f n + quadraticVariationSum f g n := by
  induction n with
  | zero =>
      grind [rightStieltjesSum, leftStieltjesSum, quadraticVariationSum]
  | succ n ih =>
      rw [rightStieltjesSum, leftStieltjesSum,
        quadraticVariationSum, ih]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- On an explicitly nondecreasing rational path, every endpoint displacement
from the initial point is nonnegative.  This is the finite order fact used to
control the corner rectangles in geometric integration by parts. -/
theorem endpointDifference_nonneg_of_step_nonnegative
    (u : Nat -> Rat)
    (hu : forall i, 0 <= u (i + 1) - u i) (n : Nat) :
    0 <= u n - u 0 := by
  induction n with
  | zero =>
      grind [Rat.sub_eq_add_neg]
  | succ n ih =>
      calc
        0 <= (u n - u 0) + (u (n + 1) - u n) :=
          Rat.add_nonneg ih (hu n)
        _ = u (n + 1) - u 0 := by
          grind [Rat.sub_eq_add_neg]

/-- If the two paths move in the same nondecreasing direction, the finite
corner correction is nonnegative.  Geometrically it is a sum of areas of
ordinary (not signed) corner rectangles. -/
theorem quadraticVariationSum_nonneg_of_step_nonnegative
    (u v : Nat -> Rat)
    (hu : forall i, 0 <= u (i + 1) - u i)
    (hv : forall i, 0 <= v (i + 1) - v i)
    (n : Nat) :
    0 <= quadraticVariationSum u v n := by
  induction n with
  | zero =>
      grind [quadraticVariationSum]
  | succ n ih =>
      rw [quadraticVariationSum]
      exact Rat.add_nonneg ih (Rat.mul_nonneg (hu n) (hv n))

/-- A mesh-size bound for the corner correction.  If every increment of the
first path is at most `delta` and the second path is nondecreasing, then the
entire correction is at most `delta` times the total variation of the second
path.  This is the finite estimate that will make the correction vanish on a
common rational refinement. -/
theorem quadraticVariationSum_le_stepBound_mul_endpointDifference
    (u v : Nat -> Rat) (delta : Rat)
    (hu : forall i, u (i + 1) - u i <= delta)
    (hv : forall i, 0 <= v (i + 1) - v i)
    (n : Nat) :
    quadraticVariationSum u v n <= delta * (v n - v 0) := by
  induction n with
  | zero =>
      grind [quadraticVariationSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [quadraticVariationSum]
      calc
        quadraticVariationSum u v n +
            (u (n + 1) - u n) * (v (n + 1) - v n) <=
          delta * (v n - v 0) +
            (u (n + 1) - u n) * (v (n + 1) - v n) :=
          Rat.add_le_add_right.mpr ih
        _ <= delta * (v n - v 0) +
            delta * (v (n + 1) - v n) :=
          Rat.add_le_add_left.mpr
            (Rat.mul_le_mul_of_nonneg_right (hu n) (hv n))
        _ = delta * (v (n + 1) - v 0) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- With two nondecreasing paths, the corner correction is bounded by the
product of their endpoint variations.  This is the finite rectangle form of
the usual ``variation times mesh'' estimate, before a particular mesh modulus
is supplied. -/
theorem quadraticVariationSum_le_endpointVariationProduct_of_step_nonnegative
    (u v : Nat -> Rat)
    (hu : forall i, 0 <= u (i + 1) - u i)
    (hv : forall i, 0 <= v (i + 1) - v i)
    (n : Nat) :
    quadraticVariationSum u v n <=
      (u n - u 0) * (v n - v 0) := by
  induction n with
  | zero =>
      grind [quadraticVariationSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      let du := u (n + 1) - u n
      let dv := v (n + 1) - v n
      let U := u n - u 0
      let V := v n - v 0
      have hU : 0 <= U := by
        dsimp [U]
        exact endpointDifference_nonneg_of_step_nonnegative u hu n
      have hV : 0 <= V := by
        dsimp [V]
        exact endpointDifference_nonneg_of_step_nonnegative v hv n
      have hdu : 0 <= du := by
        dsimp [du]
        exact hu n
      have hdv : 0 <= dv := by
        dsimp [dv]
        exact hv n
      have hcross : 0 <= U * dv + du * V :=
        Rat.add_nonneg (Rat.mul_nonneg hU hdv) (Rat.mul_nonneg hdu hV)
      rw [quadraticVariationSum]
      calc
        quadraticVariationSum u v n + du * dv <= U * V + du * dv := by
          exact Rat.add_le_add_right.mpr ih
        _ <= U * V + du * dv + (U * dv + du * V) := by
          grind [Rat.sub_eq_add_neg]
        _ = (U + du) * (V + dv) := by
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
        _ = (u (n + 1) - u 0) * (v (n + 1) - v 0) := by
          dsimp [U, V, du, dv]
          grind [Rat.sub_eq_add_neg]

/-- Negating both paths preserves every corner rectangle: its two signed side
increments change sign together.  This transfers the finite estimates from
increasing pieces to decreasing pieces without a Jordan decomposition. -/
theorem quadraticVariationSum_neg_neg
    (u v : Nat -> Rat) (n : Nat) :
    quadraticVariationSum (fun i => -u i) (fun i => -v i) n =
      quadraticVariationSum u v n := by
  induction n with
  | zero =>
      grind [quadraticVariationSum]
  | succ n ih =>
      rw [quadraticVariationSum, quadraticVariationSum, ih]
      grind [Rat.neg_sub, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg,
        Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- The endpoint-variation bound on an explicitly nonincreasing pair of
paths.  It is obtained by negating both paths, so the correction is still a
sum of ordinary corner areas while the endpoint variations are reversed. -/
theorem quadraticVariationSum_le_endpointVariationProduct_of_step_nonpositive
    (u v : Nat -> Rat)
    (hu : forall i, u (i + 1) - u i <= 0)
    (hv : forall i, v (i + 1) - v i <= 0)
    (n : Nat) :
    quadraticVariationSum u v n <=
      (u 0 - u n) * (v 0 - v n) := by
  have hu' : forall i, 0 <= (-u (i + 1)) - (-u i) := by
    intro i
    have h := hu i
    grind [Rat.neg_sub, Rat.sub_eq_add_neg]
  have hv' : forall i, 0 <= (-v (i + 1)) - (-v i) := by
    intro i
    have h := hv i
    grind [Rat.neg_sub, Rat.sub_eq_add_neg]
  have h := quadraticVariationSum_le_endpointVariationProduct_of_step_nonnegative
    (fun i => -u i) (fun i => -v i) hu' hv' n
  rw [quadraticVariationSum_neg_neg] at h
  calc
    quadraticVariationSum u v n <=
        ((-u n) - (-u 0)) * ((-v n) - (-v 0)) := h
    _ = (u 0 - u n) * (v 0 - v n) := by
      grind [Rat.neg_sub, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg,
        Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

/-- If the two paths have constant rational increments, their corner sum is
exactly the number of cells times one corner rectangle.  This is the finite
calculation behind the elementary mesh-vanishing schedule below. -/
theorem quadraticVariationSum_eq_nat_mul_of_constant_steps
    (u v : Nat -> Rat) (du dv : Rat)
    (hu : forall i, u (i + 1) - u i = du)
    (hv : forall i, v (i + 1) - v i = dv)
    (n : Nat) :
    quadraticVariationSum u v n = (n : Rat) * (du * dv) := by
  induction n with
  | zero =>
      grind [quadraticVariationSum]
  | succ n ih =>
      rw [quadraticVariationSum, hu, hv, ih, Rat.natCast_add]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]

/-- The rational identity path on an `n`-cell unit mesh.  It is a concrete
test case for the geometric integration-by-parts correction. -/
def unitMeshPath (n k : Nat) : Rat := (k : Rat) / (n : Rat)

/-- The unit-mesh coordinate starts at the exact rational left endpoint. -/
theorem unitMeshPath_zero (n : Nat) :
    unitMeshPath n 0 = 0 := by
  unfold unitMeshPath
  rw [Rat.div_def]
  simp

/-- On a positive unit mesh, the final coordinate is the exact right
endpoint.  This is the endpoint normalization used by the concrete
finite integration-by-parts calculation. -/
theorem unitMeshPath_endpoint {n : Nat} (hn : 0 < n) :
    unitMeshPath n n = 1 := by
  unfold unitMeshPath
  rw [Rat.div_def]
  have hne : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  exact Rat.mul_inv_cancel _ hne

/-- A family of interval boxes is weakly ordered when every earlier lower
endpoint is compatible with every later upper endpoint.  This is the
finite, box-valued order relation supplied by a nondecreasing interval
function. -/
def QInterval.WeaklyOrdered (boxes : Nat -> QInterval) : Prop :=
  forall i j, i <= j -> (boxes i).lo <= (boxes j).hi

/-- The cumulative maximum of lower endpoints.  It is a canonical rational
sample chosen from a weakly ordered family of interval boxes. -/
def QInterval.lowerEnvelope (boxes : Nat -> QInterval) : Nat -> Rat
  | 0 => (boxes 0).lo
  | n + 1 => max (QInterval.lowerEnvelope boxes n) (boxes (n + 1)).lo

theorem QInterval.lowerEnvelope_le_succ
    (boxes : Nat -> QInterval) (n : Nat) :
    QInterval.lowerEnvelope boxes n <= QInterval.lowerEnvelope boxes (n + 1) := by
  simp only [QInterval.lowerEnvelope]
  grind

theorem QInterval.boxLower_le_lowerEnvelope
    (boxes : Nat -> QInterval) (n : Nat) :
    (boxes n).lo <= QInterval.lowerEnvelope boxes n := by
  induction n with
  | zero =>
      exact Rat.le_refl
  | succ n _ =>
      simp only [QInterval.lowerEnvelope]
      grind

/-- Every cumulative lower-envelope sample is below the upper endpoint of
every later box in a weakly ordered family. -/
theorem QInterval.lowerEnvelope_le_boxUpper
    (boxes : Nat -> QInterval) (hboxes : QInterval.WeaklyOrdered boxes) :
    forall n j, n <= j ->
      QInterval.lowerEnvelope boxes n <= (boxes j).hi := by
  intro n
  induction n with
  | zero =>
      intro j hj
      simpa [QInterval.lowerEnvelope] using hboxes 0 j hj
  | succ n ih =>
      intro j hj
      simp only [QInterval.lowerEnvelope]
      have hprev := ih j (Nat.le_trans (Nat.le_succ n) hj)
      have hcurrent := hboxes (n + 1) j hj
      grind

/-- The lower envelope is a nondecreasing rational path. -/
theorem QInterval.lowerEnvelope_step_nonnegative
    (boxes : Nat -> QInterval) (n : Nat) :
    0 <= QInterval.lowerEnvelope boxes (n + 1) -
      QInterval.lowerEnvelope boxes n := by
  have h := QInterval.lowerEnvelope_le_succ boxes n
  grind [Rat.sub_eq_add_neg]

/-- On a weakly ordered family, the lower-envelope sample lies in the box at
the same index.  This is the finite monotone-sampling lift used by the
integration-by-parts corner estimate. -/
theorem QInterval.lowerEnvelope_mem
    (boxes : Nat -> QInterval) (hboxes : QInterval.WeaklyOrdered boxes)
    (n : Nat) :
    And ((boxes n).lo <= QInterval.lowerEnvelope boxes n)
      (QInterval.lowerEnvelope boxes n <= (boxes n).hi) :=
  ⟨QInterval.boxLower_le_lowerEnvelope boxes n,
    QInterval.lowerEnvelope_le_boxUpper boxes hboxes n n (Nat.le_refl n)⟩

/-- A selected rational point of an interval is at most one box width above
the lower endpoint. -/
theorem QInterval.point_sub_lower_le_width {I : QInterval} {x : Rat}
    (hx : x <= I.hi) :
    x - I.lo <= I.width := by
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- A selected rational point of an interval is at most one box width below
the upper endpoint. -/
theorem QInterval.upper_sub_point_le_width {I : QInterval} {x : Rat}
    (hx : I.lo <= x) :
    I.hi - x <= I.width := by
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- Unit-mesh coordinates are nonnegative, even at the degenerate
zero-cell mesh where rational division returns zero. -/
theorem unitMeshPath_nonnegative (n k : Nat) :
    0 <= unitMeshPath n k := by
  cases n with
  | zero =>
      unfold unitMeshPath
      rw [Rat.div_def]
      simp
  | succ n =>
      unfold unitMeshPath
      rw [Rat.div_def]
      have hden : 0 < ((n + 1 : Nat) : Rat) :=
        (Rat.natCast_pos).2 (Nat.succ_pos n)
      exact Rat.mul_nonneg Rat.natCast_nonneg
        (Rat.le_of_lt ((Rat.inv_pos).2 hden))

/-- Unit-mesh coordinates preserve the natural-number order. -/
theorem unitMeshPath_monotone (n i j : Nat) (hij : i <= j) :
    unitMeshPath n i <= unitMeshPath n j := by
  cases n with
  | zero =>
      unfold unitMeshPath
      rw [Rat.div_def, Rat.div_def]
      simp
  | succ n =>
      unfold unitMeshPath
      rw [Rat.div_def, Rat.div_def]
      have hcast : (i : Rat) <= (j : Rat) := by
        exact_mod_cast hij
      have hden : 0 < ((n + 1 : Nat) : Rat) :=
        (Rat.natCast_pos).2 (Nat.succ_pos n)
      exact Rat.mul_le_mul_of_nonneg_right hcast
        (Rat.le_of_lt ((Rat.inv_pos).2 hden))

/-- A unit-mesh coordinate does not exceed the right endpoint when its
index lies in the mesh. -/
theorem unitMeshPath_le_one (n k : Nat) (hk : k <= n) :
    unitMeshPath n k <= 1 := by
  cases n with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      unfold unitMeshPath
      rw [Rat.div_def]
      simp
      decide +kernel
  | succ n =>
      unfold unitMeshPath
      rw [Rat.div_def]
      have hcast : (k : Rat) <= ((n + 1 : Nat) : Rat) := by
        exact_mod_cast hk
      have hden : 0 < ((n + 1 : Nat) : Rat) :=
        (Rat.natCast_pos).2 (Nat.succ_pos n)
      have hden_ne : ((n + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hden
      calc
        (k : Rat) * ((n + 1 : Nat) : Rat)⁻¹ <=
            ((n + 1 : Nat) : Rat) * ((n + 1 : Nat) : Rat)⁻¹ :=
          Rat.mul_le_mul_of_nonneg_right hcast
            (Rat.le_of_lt ((Rat.inv_pos).2 hden))
        _ = 1 := by
          grind [Rat.mul_inv_cancel]

/-- Every increment of the unit mesh path is exactly `1/n`. -/
theorem unitMeshPath_step (n k : Nat) :
    unitMeshPath n (k + 1) - unitMeshPath n k = 1 / (n : Rat) := by
  unfold unitMeshPath
  rw [Rat.natCast_add, Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- On the positive `n`-cell unit mesh the corner correction is exactly
`1/n`.  This is an explicit rational equality, not a completeness-based
limit assertion. -/
theorem unitMeshPath_quadraticVariation {n : Nat} (hn : 0 < n) :
    quadraticVariationSum (unitMeshPath n) (unitMeshPath n) n =
      1 / (n : Rat) := by
  rw [quadraticVariationSum_eq_nat_mul_of_constant_steps
    (unitMeshPath n) (unitMeshPath n) (1 / (n : Rat)) (1 / (n : Rat))
    (unitMeshPath_step n) (unitMeshPath_step n)]
  have hnat : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-! The square-chain bracket becomes a concrete unit-mesh estimate.  This is
the finite rational computation behind the elementary certificate
`integral of 2x on [0,1] = 1`; its error is exactly the quadratic variation
`1/n`. -/

theorem unitMeshPath_square_left_bounds {n : Nat} (hn : 0 < n) :
    1 - 1 / (n : Rat) <=
        2 * leftStieltjesSum (unitMeshPath n) (unitMeshPath n) n /\
      2 * leftStieltjesSum (unitMeshPath n) (unitMeshPath n) n <= 1 := by
  have hvariation :
      0 <= quadraticVariationSum (unitMeshPath n) (unitMeshPath n) n := by
    exact quadraticVariationSum_nonneg_of_step_nonnegative
      (unitMeshPath n) (unitMeshPath n)
      (fun i => by
        rw [unitMeshPath_step, Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
      (fun i => by
        rw [unitMeshPath_step, Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn))) n
  have hvariation_le :
      quadraticVariationSum (unitMeshPath n) (unitMeshPath n) n <=
        1 / (n : Rat) := by
    rw [unitMeshPath_quadraticVariation hn]
    exact Rat.le_refl
  have h := finiteSquareStieltjes_left_bounds
    (unitMeshPath n) n (1 / (n : Rat)) hvariation hvariation_le
  rw [unitMeshPath_endpoint hn, unitMeshPath_zero] at h
  constructor <;> grind [h.1, h.2]

theorem unitMeshPath_square_left_sum_exact {n : Nat} (hn : 0 < n) :
    2 * leftStieltjesSum (unitMeshPath n) (unitMeshPath n) n =
      1 - 1 / (n : Rat) := by
  have h := finiteSquareStieltjes_chain
    (unitMeshPath n) n
  rw [unitMeshPath_endpoint hn, unitMeshPath_zero,
    unitMeshPath_quadraticVariation hn] at h
  grind

/-! The finite square calculation can itself be exposed as a raw real.  At
stage `n`, use the certified lower bound from the `(n+1)`-cell computation and
the exact upper bound.  This is a concrete example of turning a finite
rectangle proof into a shrinking rational-interval algorithm. -/

def unitMeshSquareIntegralRaw : RealCompute where
  compute n :=
    { lo := 1 - 1 / (((n + 1 : Nat) : Rat)), hi := 1 }

private theorem one_div_nat_antitone_succ {n m : Nat} (hnm : n <= m) :
    1 / (((m + 1 : Nat) : Rat)) <=
      1 / (((n + 1 : Nat) : Rat)) := by
  have hnpos : 0 < (n + 1 : Nat) := Nat.succ_pos n
  have hmpos : 0 < (m + 1 : Nat) := Nat.succ_pos m
  apply Rat.le_of_mul_le_mul_right
    (c := ((n + 1 : Nat) : Rat) * ((m + 1 : Nat) : Rat))
  · calc
      (1 / (((m + 1 : Nat) : Rat))) *
          (((n + 1 : Nat) : Rat) * ((m + 1 : Nat) : Rat)) =
          ((n + 1 : Nat) : Rat) := by
        have hmne : ((m + 1 : Nat) : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hmpos)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= ((m + 1 : Nat) : Rat) := by exact_mod_cast (Nat.succ_le_succ hnm)
      _ = (1 / (((n + 1 : Nat) : Rat))) *
          (((n + 1 : Nat) : Rat) * ((m + 1 : Nat) : Rat)) := by
        have hnne : ((n + 1 : Nat) : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hnpos)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hnpos)
      ((Rat.natCast_pos).2 hmpos)

theorem unitMeshSquareIntegralRaw_valid : unitMeshSquareIntegralRaw.Valid := by
  unfold unitMeshSquareIntegralRaw RealCompute.Valid RealCompute.ValidCompute
  constructor
  · intro n
    unfold QInterval.width
    have hpos : 0 < (1 / (((n + 1 : Nat) : Rat)) : Rat) :=
      one_div_nat_pos (Nat.succ_pos n)
    grind [Rat.sub_eq_add_neg]
  constructor
  · intro n m hnm
    have hnpos : 0 < (n + 1 : Nat) := Nat.succ_pos n
    have hmpos : 0 < (m + 1 : Nat) := Nat.succ_pos m
    have hrecip := one_div_nat_antitone_succ hnm
    have hmrecip : 0 <= (1 / (((m + 1 : Nat) : Rat)) : Rat) :=
      Rat.le_of_lt (one_div_nat_pos hmpos)
    constructor
    · grind [Rat.sub_eq_add_neg]
    constructor <;> grind [Rat.sub_eq_add_neg]
  · apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]

theorem unitMeshSquareIntegralRaw_equiv_one :
    unitMeshSquareIntegralRaw.Equiv (RealCompute.ofRat 1) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    unitMeshSquareIntegralRaw (RealCompute.ofRat 1) n n).2
  rw [RealCompute.ofRat_compute]
  unfold unitMeshSquareIntegralRaw QInterval.Overlaps
  have hpos : 0 <= (1 / (((n + 1 : Nat) : Rat)) : Rat) :=
    Rat.le_of_lt (one_div_nat_pos (Nat.succ_pos n))
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem unitMeshSquareIntegralRaw_lower_eq_left_sum (n : Nat) :
    (unitMeshSquareIntegralRaw.compute n).lo =
      2 * leftStieltjesSum (unitMeshPath (n + 1))
        (unitMeshPath (n + 1)) (n + 1) := by
  rw [unitMeshPath_square_left_sum_exact (Nat.succ_pos n)]
  rfl

/-- A fully explicit epsilon schedule for the unit-mesh corner correction.
Choosing `n = eps.den + 1` makes the rational correction at most `eps`. -/
theorem unitMeshPath_quadraticVariation_le_epsilon (eps : QPos) :
    quadraticVariationSum (unitMeshPath (eps.val.den + 1))
      (unitMeshPath (eps.val.den + 1)) (eps.val.den + 1) <= eps.val := by
  rw [unitMeshPath_quadraticVariation (Nat.succ_pos _)]
  exact one_div_den_succ_le_of_pos eps.property

/-- The unit-mesh coordinate path supplies the exact one-over-n first-increment
bound needed for integration by parts against an arbitrary nondecreasing
sample path.  This is the finite corner estimate for the future
x-times-arctangent calculation on the unit interval. -/
theorem unitMeshPath_quadraticVariation_le_one_div_mul_endpointDifference
    (n : Nat) (v : Nat -> Rat)
    (hv : forall i, 0 <= v (i + 1) - v i) :
    quadraticVariationSum (unitMeshPath n) v n <=
      (1 / (n : Rat)) * (v n - v 0) :=
  quadraticVariationSum_le_stepBound_mul_endpointDifference
    (unitMeshPath n) v (1 / (n : Rat))
    (fun i => by
      rw [unitMeshPath_step]
      exact Rat.le_refl) hv n

private theorem riemannLeftInterval_point_fold_eq
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi)
    (xs : List Nat) (acc : QInterval) (hacc : acc.lo = acc.hi) :
    (xs.foldl
      (fun acc k =>
        let I := g.compute (leftPoint a b subdivisions k) prec
        { lo := acc.lo + mesh a b subdivisions * I.lo,
          hi := acc.hi + mesh a b subdivisions * I.hi })
      acc).lo =
    (xs.foldl
      (fun acc k =>
        let I := g.compute (leftPoint a b subdivisions k) prec
        { lo := acc.lo + mesh a b subdivisions * I.lo,
          hi := acc.hi + mesh a b subdivisions * I.hi })
      acc).hi := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons k rest ih =>
      apply ih
      dsimp
      rw [hacc, hpoint (leftPoint a b subdivisions k)]

theorem riemannLeftInterval_point_eq
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi) :
    (riemannLeftInterval g a b subdivisions prec).lo =
      (riemannLeftInterval g a b subdivisions prec).hi := by
  unfold riemannLeftInterval
  exact riemannLeftInterval_point_fold_eq
    g a b subdivisions prec hpoint (List.range subdivisions)
    { lo := 0, hi := 0 } rfl

theorem riemannLeftInterval_point_width_zero
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi) :
    (riemannLeftInterval g a b subdivisions prec).width = 0 := by
  have h := riemannLeftInterval_point_eq
    g a b subdivisions prec hpoint
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

namespace RealFunRaw

def add (f g : RealFunRaw) : RealFunRaw where
  domain := fun x => f.domain x /\ g.domain x
  compute := fun x n =>
    let F := f.compute x n
    let G := g.compute x n
    { lo := F.lo + G.lo, hi := F.hi + G.hi }

/-! Pointwise addition preserves the finite interval certificate interface. -/
theorem add_valid {f g : RealFunRaw} (hf : f.Valid) (hg : g.Valid) :
    (add f g).Valid := by
  intro x hx
  let X : RealCompute := { compute := f.compute x }
  let Y : RealCompute := { compute := g.compute x }
  have hX : X.Valid := by
    simpa [X, RealCompute.Valid, RealFunRaw.applyCompute] using hf x hx.1
  have hY : Y.Valid := by
    simpa [Y, RealCompute.Valid, RealFunRaw.applyCompute] using hg x hx.2
  have hsum : (X + Y).Valid := RealCompute.add_valid hX hY
  change RealCompute.ValidCompute (RealCompute.addCompute X Y) at hsum
  change RealCompute.ValidCompute (RealCompute.addCompute X Y)
  exact hsum

def scaleRat (r : Rat) (f : RealFunRaw) : RealFunRaw where
  domain := f.domain
  compute := fun x n =>
    let F := f.compute x n
    if 0 <= r then
      { lo := r * F.lo, hi := r * F.hi }
    else
      { lo := r * F.hi, hi := r * F.lo }

/-- Pointwise interval multiplication on the common rational domain.

Validity is intentionally supplied separately: unlike addition, a shrinking
product enclosure needs a finite bound on both factors.  The positive bounded
certificate below is the first reusable case needed by product rules and
integration by parts. -/
def mul (f g : RealFunRaw) : RealFunRaw where
  domain := fun x => f.domain x /\ g.domain x
  compute := fun x n =>
    QBox.mulRealInterval
      (f.compute x n).lo (f.compute x n).hi
      (g.compute x n).lo (g.compute x n).hi

/-- A rational pointwise product is a valid interval-real function whenever
each factor has a positive rational enclosure bound at that point.  The bound
may depend on the rational input, which is sufficient for the foundational
function notion and avoids any hidden compactness argument. -/
theorem mul_valid_of_nonneg_bounded
    {f g : RealFunRaw} (hf : f.Valid) (hg : g.Valid)
    (hfbounds : forall (x : Rat) (_hx : f.domain x), Exists fun B : Rat =>
      0 < B /\ forall n, 0 <= (f.compute x n).lo /\ (f.compute x n).hi <= B)
    (hgbounds : forall (x : Rat) (_hx : g.domain x), Exists fun B : Rat =>
      0 < B /\ forall n, 0 <= (g.compute x n).lo /\ (g.compute x n).hi <= B) :
    (mul f g).Valid := by
  intro x hx
  rcases hfbounds x hx.1 with ⟨Bx, hBx, hxbounds⟩
  rcases hgbounds x hx.2 with ⟨By, hBy, hybounds⟩
  let X : RealCompute := { compute := f.compute x }
  let Y : RealCompute := { compute := g.compute x }
  have hX : X.Valid := by
    simpa [X, RealCompute.Valid, RealFunRaw.applyCompute] using hf x hx.1
  have hY : Y.Valid := by
    simpa [Y, RealCompute.Valid, RealFunRaw.applyCompute] using hg x hx.2
  have hproduct : (X * Y).Valid :=
    RealCompute.mul_valid_of_nonneg_bounded hX hY hBx hBy hxbounds hybounds
  change RealCompute.ValidCompute (RealCompute.mulCompute X Y) at hproduct
  change RealCompute.ValidCompute (RealCompute.mulCompute X Y)
  exact hproduct

end RealFunRaw

def precisionAtStage (n : Nat) : QPos :=
  if hn : n = 0 then
      { val := 1, property := by grind }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }

/-- Later natural stages request no coarser rational precision. -/
theorem precisionAtStage_antitone {m n : Nat} (hmn : m <= n) :
    (precisionAtStage n).val <= (precisionAtStage m).val := by
  have one_div_nat_le_one_div_nat_of_le {a b : Nat}
      (ha : 0 < a) (hab : a <= b) :
      1 / (b : Rat) <= 1 / (a : Rat) := by
    let A : Rat := (a : Rat)
    let B : Rat := (b : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 ha
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.lt_of_lt_of_le ha hab)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hAleB : A <= B := by
      dsimp [A, B]
      exact Rat.natCast_le_natCast.2 hab
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (1 / B) * (A * B) = A := by
          rw [Rat.div_def]
          have hcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= B := hAleB
        _ = (1 / A) * (A * B) := by
          rw [Rat.div_def]
          have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hABpos
  by_cases hm : m = 0
  · subst m
    by_cases hn : n = 0
    · simp [precisionAtStage, hn]
    · simpa [precisionAtStage, hn,
          show (1 / (1 : Rat)) = 1 by decide +kernel] using
        (one_div_nat_le_one_div_nat_of_le
          (a := 1) (b := n) (by omega) (Nat.one_le_iff_ne_zero.2 hn))
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hn : n ≠ 0 := by omega
    simpa [precisionAtStage, hm, hn] using
      (one_div_nat_le_one_div_nat_of_le hmpos hmn)

def intervalCloseAtPrecision (I J : QInterval) (n : Nat) : Prop :=
  QInterval.CloseAt I J (precisionAtStage n)

/-- Precision-indexed quantitative closeness for enclosures of possibly
distinct nearby values. -/
def intervalNearAtPrecision (I J : QInterval) (n : Nat) : Prop :=
  QInterval.NearAt I J (precisionAtStage n)

namespace QInterval

/-- A weak interval order: the two interval enclosures are compatible with
some value of the left endpoint being at most some value of the right endpoint.
This is the order notion used for qualitative monotonicity and convexity
certificates, where finite rational enclosures may still overlap. -/
def WeakLe (I J : QInterval) : Prop :=
  I.lo <= J.hi

/-- A strong interval order: every value in the left interval is at most every
value in the right interval.  This is useful for certified bounds. -/
def StrongLe (I J : QInterval) : Prop :=
  I.hi <= J.lo

def addInterval (I J : QInterval) : QInterval :=
  { lo := I.lo + J.lo, hi := I.hi + J.hi }

/-- Finite enclosure is reflexive. -/
theorem containsInterval_refl (I : QInterval) : I.ContainsInterval I := by
  unfold ContainsInterval
  exact ⟨Rat.le_refl, Rat.le_refl⟩

/-- Finite interval enclosure composes in the expected direction. -/
theorem ContainsInterval.trans {A B C : QInterval}
    (hAB : A.ContainsInterval B) (hBC : B.ContainsInterval C) :
    A.ContainsInterval C := by
  unfold ContainsInterval at *
  exact ⟨Rat.le_trans hAB.1 hBC.1, Rat.le_trans hBC.2 hAB.2⟩

/-- An outer interval overlaps every ordered interval that it encloses. -/
theorem overlaps_of_contains_right {outer inner : QInterval}
    (hcontains : outer.ContainsInterval inner)
    (hordered : 0 <= inner.width) : outer.Overlaps inner := by
  unfold ContainsInterval Overlaps width at *
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Adding two enclosing intervals still encloses the sum of the inner
intervals.  This is the finite algebra used to assemble cellwise FTC bounds. -/
theorem addInterval_contains {A B C D : QInterval}
    (hAC : A.ContainsInterval C) (hBD : B.ContainsInterval D) :
    (addInterval A B).ContainsInterval (addInterval C D) := by
  unfold ContainsInterval addInterval at *
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- The degenerate zero interval is an additive identity for finite interval
addition. -/
theorem zero_addInterval (I : QInterval) :
    addInterval { lo := 0, hi := 0 } I = I := by
  cases I
  unfold addInterval
  congr <;> grind

/-- Interval addition adds enclosure widths exactly. -/
theorem addInterval_width (I J : QInterval) :
    (addInterval I J).width = I.width + J.width := by
  unfold addInterval QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

end QInterval

/-- Adding two finite enclosure comparisons adds their error budgets.  The
precision hypothesis is explicit so callers can choose a finer internal stage
without invoking a limit or completeness principle. -/
theorem intervalNearAtPrecision_addInterval
    {I J K L : QInterval} {m n : Nat}
    (hIJ : intervalNearAtPrecision I J m)
    (hKL : intervalNearAtPrecision K L m)
    (hprecision : 2 * (precisionAtStage m).val <=
      (precisionAtStage n).val) :
    intervalNearAtPrecision (QInterval.addInterval I K)
      (QInterval.addInterval J L) n := by
  unfold intervalNearAtPrecision QInterval.NearAt at hIJ hKL ⊢
  rcases hIJ with ⟨hIleft, hIright, hIwidth, hJwidth⟩
  rcases hKL with ⟨hKleft, hKright, hKwidth, hLwidth⟩
  unfold QInterval.addInterval
  constructor
  · calc
      I.lo + K.lo <= (J.hi + (precisionAtStage m).val) +
          (L.hi + (precisionAtStage m).val) := by grind
      _ = J.hi + L.hi +
          2 * (precisionAtStage m).val := by
        grind [Rat.add_assoc, Rat.add_comm]
      _ <= J.hi + L.hi + (precisionAtStage n).val := by
        exact (Rat.add_le_add_left).2 hprecision
  constructor
  · calc
      J.lo + L.lo <= (I.hi + (precisionAtStage m).val) +
          (K.hi + (precisionAtStage m).val) := by grind
      _ = I.hi + K.hi +
          2 * (precisionAtStage m).val := by
        grind [Rat.add_assoc, Rat.add_comm]
      _ <= I.hi + K.hi + (precisionAtStage n).val := by
        exact (Rat.add_le_add_left).2 hprecision
  constructor
  · change I.hi + K.hi - (I.lo + K.lo) <=
      (precisionAtStage n).val
    calc
      I.hi + K.hi - (I.lo + K.lo) = I.width + K.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      _ <= 2 * (precisionAtStage m).val := by
        grind
      _ <= (precisionAtStage n).val := hprecision
  · change J.hi + L.hi - (J.lo + L.lo) <=
      (precisionAtStage n).val
    calc
      J.hi + L.hi - (J.lo + L.lo) = J.width + L.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      _ <= 2 * (precisionAtStage m).val := by
        grind
      _ <= (precisionAtStage n).val := hprecision

namespace QInterval

def scaleByRat (r : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    { lo := r * I.lo, hi := r * I.hi }
  else
    { lo := r * I.hi, hi := r * I.lo }

/-- Positive rational scaling preserves finite interval containment.  This is
the scaling direction used when a derivative bound is converted into an
endpoint-difference bound on a rational cell. -/
theorem scaleByRat_contains_of_nonneg {r : Rat} (hr : 0 <= r)
    {outer inner : QInterval} (hcontains : outer.ContainsInterval inner) :
    (scaleByRat r outer).ContainsInterval (scaleByRat r inner) := by
  unfold scaleByRat QInterval.ContainsInterval
  simp only [if_pos hr]
  constructor
  · exact Rat.mul_le_mul_of_nonneg_left hcontains.1 hr
  · exact Rat.mul_le_mul_of_nonneg_left hcontains.2 hr

/-- Arbitrary rational scaling preserves interval containment; for a negative
scale the endpoint order is reversed by `scaleByRat`. -/
theorem scaleByRat_contains {r : Rat}
    {outer inner : QInterval} (hcontains : outer.ContainsInterval inner) :
    (scaleByRat r outer).ContainsInterval (scaleByRat r inner) := by
  by_cases hr : 0 <= r
  · exact scaleByRat_contains_of_nonneg hr hcontains
  · have hrneg : r < 0 := Rat.not_le.mp hr
    unfold scaleByRat QInterval.ContainsInterval
    simp only [if_neg hr]
    constructor
    · exact rat_mul_le_mul_of_nonpos_left hcontains.2 (Rat.le_of_lt hrneg)
    · exact rat_mul_le_mul_of_nonpos_left hcontains.1 (Rat.le_of_lt hrneg)

/-- Positive rational scaling multiplies enclosure width by the scale. -/
theorem scaleByRat_width_of_nonneg {r : Rat} (hr : 0 <= r) (I : QInterval) :
    (scaleByRat r I).width = r * I.width := by
  unfold scaleByRat QInterval.width
  rw [if_pos hr]
  grind [Rat.sub_eq_add_neg, Rat.mul_add]

/-- Sign-complete width law for rational interval scaling. -/
theorem scaleByRat_width (r : Rat) (I : QInterval) :
    (scaleByRat r I).width = qabs r * I.width := by
  by_cases hr : 0 <= r
  · simpa [qabs_eq_self_of_nonneg hr] using scaleByRat_width_of_nonneg hr I
  · have hrneg : r < 0 := Rat.not_le.mp hr
    unfold scaleByRat QInterval.width
    rw [if_neg hr]
    rw [qabs_eq_neg_of_nonpos (Rat.le_of_lt hrneg)]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]

def subInterval (I J : QInterval) : QInterval :=
  { lo := I.lo - J.hi, hi := I.hi - J.lo }

/-- The width of an interval difference is the sum of the operand widths. -/
theorem subInterval_width (I J : QInterval) :
    (subInterval I J).width = I.width + J.width := by
  unfold subInterval QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-- Rational scaling commutes with interval subtraction, including the
negative-scale endpoint reversal. -/
theorem scaleByRat_subInterval (r : Rat) (I J : QInterval) :
    scaleByRat r (subInterval I J) =
      subInterval (scaleByRat r I) (scaleByRat r J) := by
  by_cases hr : 0 <= r
  · simp [scaleByRat, subInterval, hr]
    constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add]
  · simp [scaleByRat, subInterval, hr]
    constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add]

/-- Subtraction propagates interval containment with the endpoint reversal
required for the subtracted box. -/
theorem subInterval_contains
    {outerLeft outerRight innerLeft innerRight : QInterval}
    (hleft : outerLeft.ContainsInterval innerLeft)
    (hright : outerRight.ContainsInterval innerRight) :
    (subInterval outerLeft outerRight).ContainsInterval
      (subInterval innerLeft innerRight) := by
  unfold subInterval QInterval.ContainsInterval at *
  constructor <;> grind

def divByRat (I : QInterval) (h : Rat) : QInterval :=
  scaleByRat (1 / h) I

/-! Division is only used as an interval operation when its rational
denominator is known positive.  Keeping that hypothesis explicit prevents a
secant or average enclosure from silently reversing its endpoints. -/
theorem divByRat_contains_of_pos {h : Rat} (hh : 0 < h)
    {outer inner : QInterval} (hcontains : outer.ContainsInterval inner) :
    (divByRat outer h).ContainsInterval (divByRat inner h) := by
  have hinv : 0 < (1 / h) := by
    simpa [Rat.div_def] using (Rat.inv_pos.mpr hh)
  apply scaleByRat_contains_of_nonneg
  · exact Rat.le_of_lt hinv
  · exact hcontains

theorem divByRat_width_of_pos {h : Rat} (hh : 0 < h) (I : QInterval) :
    (divByRat I h).width = (1 / h) * I.width := by
  have hinv : 0 < (1 / h) := by
    simpa [Rat.div_def] using (Rat.inv_pos.mpr hh)
  apply scaleByRat_width_of_nonneg
  exact Rat.le_of_lt hinv

/-- Interval enclosure of `(Fy - Fx) / dx`.  For a secant slope, `dx` will be
the rational difference `y - x`; the caller carries the proof that `x < y`. -/
def slopeBetween (Fy Fx : QInterval) (dx : Rat) : QInterval :=
  divByRat (subInterval Fy Fx) dx

/-! A positive-step secant is the composition of interval subtraction and
positive rational division. -/
theorem slopeBetween_contains_of_pos {dx : Rat} (hdx : 0 < dx)
    {outerY outerX innerY innerX : QInterval}
    (hy : outerY.ContainsInterval innerY)
    (hx : outerX.ContainsInterval innerX) :
    (slopeBetween outerY outerX dx).ContainsInterval
      (slopeBetween innerY innerX dx) := by
  unfold slopeBetween
  exact divByRat_contains_of_pos hdx (subInterval_contains hy hx)

/-- A positive-step secant width is the endpoint-box width divided by the
step.  This exposes the finite error budget before any derivative theorem is
applied. -/
theorem slopeBetween_width_of_pos {dx : Rat} (hdx : 0 < dx)
    (Fy Fx : QInterval) :
    (slopeBetween Fy Fx dx).width =
      (1 / dx) * (Fy.width + Fx.width) := by
  unfold slopeBetween
  rw [divByRat_width_of_pos hdx, subInterval_width]

end QInterval

/-! The finite trapezoid fold is exactly one half of the sum of the left and
right endpoint folds.  This is a syntactic rational identity between finite
computations, not an assertion that the three limiting integrals exist. -/
theorem riemannTrapezoidInterval_eq_half_add_left_right
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat) :
    riemannTrapezoidInterval g a b subdivisions prec =
      QInterval.scaleByRat (1 / 2)
        (QInterval.addInterval
          (riemannLeftInterval g a b subdivisions prec)
          (riemannRightInterval g a b subdivisions prec)) := by
  unfold riemannTrapezoidInterval riemannLeftInterval riemannRightInterval
  let stepL : QInterval -> Nat -> QInterval := fun acc k =>
    let I := g.compute (leftPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepR : QInterval -> Nat -> QInterval := fun acc k =>
    let I := g.compute (rightPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepT : QInterval -> Nat -> QInterval := fun acc k =>
    let L := g.compute (leftPoint a b subdivisions k) prec
    let R := g.compute (rightPoint a b subdivisions k) prec
    { lo := acc.lo + (mesh a b subdivisions / 2) * (L.lo + R.lo),
      hi := acc.hi + (mesh a b subdivisions / 2) * (L.hi + R.hi) }
  have hstep : forall k (AL AR : QInterval),
      stepT (QInterval.scaleByRat (1 / 2) (QInterval.addInterval AL AR)) k =
        QInterval.scaleByRat (1 / 2)
          (QInterval.addInterval (stepL AL k) (stepR AR k)) := by
    intro k AL AR
    dsimp [stepL, stepR, stepT, QInterval.scaleByRat,
      QInterval.addInterval]
    simp only [if_pos (by decide +kernel : (0 : Rat) <= 1 / 2)]
    grind [Rat.mul_assoc, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.add_left_comm]
  have hfold : forall (xs : List Nat) (AL AR : QInterval),
      xs.foldl stepT (QInterval.scaleByRat (1 / 2)
        (QInterval.addInterval AL AR)) =
        QInterval.scaleByRat (1 / 2)
          (QInterval.addInterval (xs.foldl stepL AL) (xs.foldl stepR AR)) := by
    intro xs
    induction xs with
    | nil =>
        intro AL AR
        rfl
    | cons k ks ih =>
        intro AL AR
        simp only [List.foldl]
        rw [hstep k AL AR]
        exact ih (stepL AL k) (stepR AR k)
  have hzero : QInterval.addInterval { lo := 0, hi := 0 } { lo := 0, hi := 0 } =
      { lo := 0, hi := 0 } := by
    simp [QInterval.addInterval]
    grind
  have hscalezero : QInterval.scaleByRat (1 / 2) { lo := 0, hi := 0 } =
      { lo := 0, hi := 0 } := by
    simp [QInterval.scaleByRat]
  have h := hfold (List.range subdivisions)
    { lo := 0, hi := 0 } { lo := 0, hi := 0 }
  rw [hzero, hscalezero] at h
  simpa [stepL, stepR, stepT] using h

/-- The trapezoid enclosure width is exactly the averaged width of its left
and right endpoint enclosures.  This is the finite error-budget law used when
the two endpoint evaluators have different precision schedules. -/
theorem riemannTrapezoidInterval_width_eq_half_add_left_right
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat) :
    (riemannTrapezoidInterval g a b subdivisions prec).width =
      (1 / 2) *
        ((riemannLeftInterval g a b subdivisions prec).width +
          (riemannRightInterval g a b subdivisions prec).width) := by
  rw [riemannTrapezoidInterval_eq_half_add_left_right]
  rw [QInterval.scaleByRat_width_of_nonneg
    (by decide +kernel : (0 : Rat) <= 1 / 2)]
  rw [QInterval.addInterval_width]

/-! A shared tolerance for the two endpoint schedules is inherited by the
trapezoid schedule. -/
theorem riemannTrapezoidInterval_width_le_of_left_right_width_le
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat) (eps : Rat)
    (hleft : (riemannLeftInterval g a b subdivisions prec).width <= eps)
    (hright : (riemannRightInterval g a b subdivisions prec).width <= eps) :
    (riemannTrapezoidInterval g a b subdivisions prec).width <= eps := by
  rw [riemannTrapezoidInterval_width_eq_half_add_left_right]
  have hsum :
      (riemannLeftInterval g a b subdivisions prec).width +
          (riemannRightInterval g a b subdivisions prec).width <= eps + eps := by
    grind
  have hscaled := Rat.mul_le_mul_of_nonneg_left hsum
    (by decide +kernel : (0 : Rat) <= 1 / 2)
  grind

/-! Independent endpoint evaluators may be transported through the trapezoid
schedule by overlap alone.  This is the interval-valued counterpart of the
finite identity above and is the form used by nested-radical or Taylor
providers. -/
theorem riemannTrapezoidInterval_overlap_of_samples
    (g h : RealFunRaw) (a b : Rat) (hab : a <= b)
    (subdivisions prec : Nat)
    (hleft : forall k, k < subdivisions ->
      QInterval.Overlaps
        (g.compute (leftPoint a b subdivisions k) prec)
        (h.compute (leftPoint a b subdivisions k) prec))
    (hright : forall k, k < subdivisions ->
      QInterval.Overlaps
        (g.compute (rightPoint a b subdivisions k) prec)
        (h.compute (rightPoint a b subdivisions k) prec)) :
    QInterval.Overlaps
      (riemannTrapezoidInterval g a b subdivisions prec)
      (riemannTrapezoidInterval h a b subdivisions prec) := by
  unfold riemannTrapezoidInterval
  have hmesh : 0 <= mesh a b subdivisions := by
    by_cases hn : 0 < subdivisions
    · exact mesh_nonneg_of_le hn hab
    · have hz : subdivisions = 0 := by omega
      simp [mesh, hz]
  have hhalf : 0 <= mesh a b subdivisions / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hmesh (by decide +kernel)
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < subdivisions) ->
      forall (accG accH : QInterval), QInterval.Overlaps accG accH ->
      QInterval.Overlaps
        (xs.foldl
          (fun acc k =>
            let L := g.compute (leftPoint a b subdivisions k) prec
            let R := g.compute (rightPoint a b subdivisions k) prec
            { lo := acc.lo + (mesh a b subdivisions / 2) * (L.lo + R.lo),
              hi := acc.hi + (mesh a b subdivisions / 2) * (L.hi + R.hi) })
          accG)
        (xs.foldl
          (fun acc k =>
            let L := h.compute (leftPoint a b subdivisions k) prec
            let R := h.compute (rightPoint a b subdivisions k) prec
            { lo := acc.lo + (mesh a b subdivisions / 2) * (L.lo + R.lo),
              hi := acc.hi + (mesh a b subdivisions / 2) * (L.hi + R.hi) })
          accH) := by
    intro xs
    induction xs with
    | nil =>
        intro _ accG accH hover
        exact hover
    | cons k ks ih =>
        intro hmem
        have hk : k < subdivisions := hmem k (by simp)
        have hks : forall j, j ∈ ks -> j < subdivisions := by
          intro j hj
          exact hmem j (by simp [hj])
        intro accG accH hover
        have hL := hleft k hk
        have hR := hright k hk
        have hstep : QInterval.Overlaps
            { lo := accG.lo + (mesh a b subdivisions / 2) *
                ((g.compute (leftPoint a b subdivisions k) prec).lo +
                  (g.compute (rightPoint a b subdivisions k) prec).lo),
              hi := accG.hi + (mesh a b subdivisions / 2) *
                ((g.compute (leftPoint a b subdivisions k) prec).hi +
                  (g.compute (rightPoint a b subdivisions k) prec).hi) }
            { lo := accH.lo + (mesh a b subdivisions / 2) *
                ((h.compute (leftPoint a b subdivisions k) prec).lo +
                  (h.compute (rightPoint a b subdivisions k) prec).lo),
              hi := accH.hi + (mesh a b subdivisions / 2) *
                ((h.compute (leftPoint a b subdivisions k) prec).hi +
                  (h.compute (rightPoint a b subdivisions k) prec).hi) } := by
          unfold QInterval.Overlaps at hover hL hR ⊢
          constructor
          · have hsum :
                (g.compute (leftPoint a b subdivisions k) prec).lo +
                    (g.compute (rightPoint a b subdivisions k) prec).lo <=
                  (h.compute (leftPoint a b subdivisions k) prec).hi +
                    (h.compute (rightPoint a b subdivisions k) prec).hi := by
              grind
            have hscaled := Rat.mul_le_mul_of_nonneg_left hsum hhalf
            grind
          · have hsum :
                (h.compute (leftPoint a b subdivisions k) prec).lo +
                    (h.compute (rightPoint a b subdivisions k) prec).lo <=
                  (g.compute (leftPoint a b subdivisions k) prec).hi +
                    (g.compute (rightPoint a b subdivisions k) prec).hi := by
              grind
            have hscaled := Rat.mul_le_mul_of_nonneg_left hsum hhalf
            grind
        simpa using ih hks _ _ hstep
  exact hfold (List.range subdivisions)
    (by intro k hk; exact List.mem_range.mp hk)
    { lo := 0, hi := 0 } { lo := 0, hi := 0 } (by
      simp [QInterval.Overlaps])

/-! Exact equality of both endpoint samples gives exact equality of the
trapezoid folds. -/
theorem riemannTrapezoidInterval_congr_of_samples
    (g h : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hleft : forall k, k < subdivisions ->
      g.compute (leftPoint a b subdivisions k) prec =
        h.compute (leftPoint a b subdivisions k) prec)
    (hright : forall k, k < subdivisions ->
      g.compute (rightPoint a b subdivisions k) prec =
        h.compute (rightPoint a b subdivisions k) prec) :
    riemannTrapezoidInterval g a b subdivisions prec =
      riemannTrapezoidInterval h a b subdivisions prec := by
  unfold riemannTrapezoidInterval
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < subdivisions) ->
      forall (acc : QInterval),
      (xs.foldl
        (fun acc k =>
          let L := g.compute (leftPoint a b subdivisions k) prec
          let R := g.compute (rightPoint a b subdivisions k) prec
          { lo := acc.lo + (mesh a b subdivisions / 2) * (L.lo + R.lo),
            hi := acc.hi + (mesh a b subdivisions / 2) * (L.hi + R.hi) }) acc) =
      (xs.foldl
        (fun acc k =>
          let L := h.compute (leftPoint a b subdivisions k) prec
          let R := h.compute (rightPoint a b subdivisions k) prec
          { lo := acc.lo + (mesh a b subdivisions / 2) * (L.lo + R.lo),
            hi := acc.hi + (mesh a b subdivisions / 2) * (L.hi + R.hi) }) acc) := by
    intro xs
    induction xs with
    | nil =>
        intro _hmem acc
        rfl
    | cons k ks ih =>
        intro hmem acc
        dsimp
        rw [hleft k (hmem k (by simp)), hright k (hmem k (by simp))]
        exact ih (fun j hj => hmem j (by simp [hj])) _
  exact hfold (List.range subdivisions)
    (by intro k hk; exact List.mem_range.mp hk) { lo := 0, hi := 0 }

/-! The finite right-endpoint fold has the same pointwise-addition law as the
left-endpoint fold. -/

theorem riemannRightInterval_add
    (f g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat) :
    riemannRightInterval (RealFunRaw.add f g) a b subdivisions prec =
      QInterval.addInterval
        (riemannRightInterval f a b subdivisions prec)
        (riemannRightInterval g a b subdivisions prec) := by
  unfold riemannRightInterval
  let stepF : QInterval -> Nat -> QInterval := fun acc k =>
    let I := f.compute (rightPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepG : QInterval -> Nat -> QInterval := fun acc k =>
    let I := g.compute (rightPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepH : QInterval -> Nat -> QInterval := fun acc k =>
    let I := (RealFunRaw.add f g).compute
      (rightPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  have hstep : forall k (AF AG : QInterval),
      stepH (QInterval.addInterval AF AG) k =
        QInterval.addInterval (stepF AF k) (stepG AG k) := by
    intro k AF AG
    dsimp [stepF, stepG, stepH, RealFunRaw.add,
      QInterval.addInterval]
    grind [Rat.add_assoc, Rat.add_comm, Rat.mul_add, Rat.add_mul]
  have hfold : forall (xs : List Nat) (AF AG : QInterval),
      xs.foldl stepH (QInterval.addInterval AF AG) =
        QInterval.addInterval (xs.foldl stepF AF) (xs.foldl stepG AG) := by
    intro xs
    induction xs with
    | nil =>
        intro AF AG
        rfl
    | cons k ks ih =>
        intro AF AG
        simp only [List.foldl]
        rw [hstep k AF AG]
        exact ih (stepF AF k) (stepG AG k)
  have hzero : QInterval.addInterval { lo := 0, hi := 0 } { lo := 0, hi := 0 } =
      { lo := 0, hi := 0 } := by
    simp [QInterval.addInterval]
    grind
  have h := hfold (List.range subdivisions)
    { lo := 0, hi := 0 } { lo := 0, hi := 0 }
  rw [hzero] at h
  simpa [stepF, stepG, stepH] using h

/-! The finite rectangle fold respects pointwise addition.  This is the
algebraic core of integral linearity; validity and representation transport
remain separate certificate obligations. -/

theorem riemannLeftInterval_add
    (f g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat) :
    riemannLeftInterval (RealFunRaw.add f g) a b subdivisions prec =
      QInterval.addInterval
        (riemannLeftInterval f a b subdivisions prec)
        (riemannLeftInterval g a b subdivisions prec) := by
  unfold riemannLeftInterval
  let stepF : QInterval -> Nat -> QInterval := fun acc k =>
    let I := f.compute (leftPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepG : QInterval -> Nat -> QInterval := fun acc k =>
    let I := g.compute (leftPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepH : QInterval -> Nat -> QInterval := fun acc k =>
    let I := (RealFunRaw.add f g).compute
      (leftPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  have hstep : forall k (AF AG : QInterval),
      stepH (QInterval.addInterval AF AG) k =
        QInterval.addInterval (stepF AF k) (stepG AG k) := by
    intro k AF AG
    dsimp [stepF, stepG, stepH, RealFunRaw.add,
      QInterval.addInterval]
    grind [Rat.add_assoc, Rat.add_comm, Rat.mul_add, Rat.add_mul]
  have hfold : forall (xs : List Nat) (AF AG : QInterval),
      xs.foldl stepH (QInterval.addInterval AF AG) =
        QInterval.addInterval (xs.foldl stepF AF) (xs.foldl stepG AG) := by
    intro xs
    induction xs with
    | nil =>
        intro AF AG
        rfl
    | cons k ks ih =>
        intro AF AG
        simp only [List.foldl]
        rw [hstep k AF AG]
        exact ih (stepF AF k) (stepG AG k)
  have hzero : QInterval.addInterval { lo := 0, hi := 0 } { lo := 0, hi := 0 } =
      { lo := 0, hi := 0 } := by
    simp [QInterval.addInterval]
    grind
  have h := hfold (List.range subdivisions)
    { lo := 0, hi := 0 } { lo := 0, hi := 0 }
  rw [hzero] at h
  simpa [stepF, stepG, stepH] using h

/-! Nonnegative rational scaling also commutes with the finite rectangle
fold.  Together with `riemannLeftInterval_add`, this is the finite algebraic
core of linearity for the integral candidate. -/

theorem riemannLeftInterval_scale_of_nonneg
    {r : Rat} (hr : 0 <= r) (f : RealFunRaw) (a b : Rat)
    (subdivisions prec : Nat) :
    riemannLeftInterval (RealFunRaw.scaleRat r f) a b subdivisions prec =
      QInterval.scaleByRat r
        (riemannLeftInterval f a b subdivisions prec) := by
  unfold riemannLeftInterval
  let stepF : QInterval -> Nat -> QInterval := fun acc k =>
    let I := f.compute (leftPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepR : QInterval -> Nat -> QInterval := fun acc k =>
    let I := (RealFunRaw.scaleRat r f).compute
      (leftPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  have hstep : forall k (A : QInterval),
      stepR (QInterval.scaleByRat r A) k =
        QInterval.scaleByRat r (stepF A k) := by
    intro k A
    dsimp [stepF, stepR, RealFunRaw.scaleRat,
      QInterval.scaleByRat]
    simp only [if_pos hr]
    grind [Rat.mul_assoc, Rat.mul_add, Rat.add_mul]
  have hfold : forall (xs : List Nat) (A : QInterval),
      xs.foldl stepR (QInterval.scaleByRat r A) =
        QInterval.scaleByRat r (xs.foldl stepF A) := by
    intro xs
    induction xs with
    | nil =>
        intro A
        rfl
    | cons k ks ih =>
        intro A
        simp only [List.foldl]
        rw [hstep k A]
        exact ih (stepF A k)
  have hzero : QInterval.scaleByRat r { lo := 0, hi := 0 } =
      { lo := 0, hi := 0 } := by
    simp [QInterval.scaleByRat]
  have h := hfold (List.range subdivisions) { lo := 0, hi := 0 }
  rw [hzero] at h
  simpa [stepF, stepR] using h

/-! Negative scaling reverses interval endpoints.  The ordered-interval
hypothesis makes the mesh nonnegative, so this is still a literal finite
rectangle identity rather than a limiting argument. -/

theorem riemannLeftInterval_scale_of_neg
    {r : Rat} (hr : r < 0) (f : RealFunRaw) (a b : Rat)
    (hab : a <= b) (subdivisions prec : Nat) (hn : 0 < subdivisions) :
    riemannLeftInterval (RealFunRaw.scaleRat r f) a b subdivisions prec =
      QInterval.scaleByRat r
        (riemannLeftInterval f a b subdivisions prec) := by
  unfold riemannLeftInterval
  have hmesh : 0 <= mesh a b subdivisions := mesh_nonneg_of_le hn hab
  let stepF : QInterval -> Nat -> QInterval := fun acc k =>
    let I := f.compute (leftPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepR : QInterval -> Nat -> QInterval := fun acc k =>
    let I := (RealFunRaw.scaleRat r f).compute
      (leftPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  have hstep : forall k (A : QInterval),
      stepR (QInterval.scaleByRat r A) k =
        QInterval.scaleByRat r (stepF A k) := by
    intro k A
    dsimp [stepF, stepR, RealFunRaw.scaleRat,
      QInterval.scaleByRat]
    simp only [if_neg (by grind : ¬ 0 <= r)]
    grind [Rat.mul_assoc, Rat.mul_add, Rat.add_mul, Rat.mul_comm]
  have hfold : forall (xs : List Nat) (A : QInterval),
      xs.foldl stepR (QInterval.scaleByRat r A) =
        QInterval.scaleByRat r (xs.foldl stepF A) := by
    intro xs
    induction xs with
    | nil =>
        intro A
        rfl
    | cons k ks ih =>
        intro A
        simp only [List.foldl]
        rw [hstep k A]
        exact ih (stepF A k)
  have hzero : QInterval.scaleByRat r { lo := 0, hi := 0 } =
      { lo := 0, hi := 0 } := by
    simp [QInterval.scaleByRat]
  have h := hfold (List.range subdivisions) { lo := 0, hi := 0 }
  rw [hzero] at h
  simpa [stepF, stepR] using h

/-! Nonnegative rational scaling commutes with the right-endpoint rectangle
fold as well. -/
theorem riemannRightInterval_scale_of_nonneg
    {r : Rat} (hr : 0 <= r) (f : RealFunRaw) (a b : Rat)
    (subdivisions prec : Nat) :
    riemannRightInterval (RealFunRaw.scaleRat r f) a b subdivisions prec =
      QInterval.scaleByRat r
        (riemannRightInterval f a b subdivisions prec) := by
  unfold riemannRightInterval
  let stepF : QInterval -> Nat -> QInterval := fun acc k =>
    let I := f.compute (rightPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepR : QInterval -> Nat -> QInterval := fun acc k =>
    let I := (RealFunRaw.scaleRat r f).compute
      (rightPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  have hstep : forall k (A : QInterval),
      stepR (QInterval.scaleByRat r A) k =
        QInterval.scaleByRat r (stepF A k) := by
    intro k A
    dsimp [stepF, stepR, RealFunRaw.scaleRat,
      QInterval.scaleByRat]
    simp only [if_pos hr]
    grind [Rat.mul_assoc, Rat.mul_add, Rat.add_mul]
  have hfold : forall (xs : List Nat) (A : QInterval),
      xs.foldl stepR (QInterval.scaleByRat r A) =
        QInterval.scaleByRat r (xs.foldl stepF A) := by
    intro xs
    induction xs with
    | nil =>
        intro A
        rfl
    | cons k ks ih =>
        intro A
        simp only [List.foldl]
        rw [hstep k A]
        exact ih (stepF A k)
  have hzero : QInterval.scaleByRat r { lo := 0, hi := 0 } =
      { lo := 0, hi := 0 } := by
    simp [QInterval.scaleByRat]
  have h := hfold (List.range subdivisions) { lo := 0, hi := 0 }
  rw [hzero] at h
  simpa [stepF, stepR] using h

/-! Negative right-endpoint scaling reverses interval endpoints.  As on the
left, an ordered interval and positive subdivision count make the mesh
nonnegative, which is the only extra hypothesis needed. -/
theorem riemannRightInterval_scale_of_neg
    {r : Rat} (hr : r < 0) (f : RealFunRaw) (a b : Rat)
    (hab : a <= b) (subdivisions prec : Nat) (hn : 0 < subdivisions) :
    riemannRightInterval (RealFunRaw.scaleRat r f) a b subdivisions prec =
      QInterval.scaleByRat r
        (riemannRightInterval f a b subdivisions prec) := by
  unfold riemannRightInterval
  have hmesh : 0 <= mesh a b subdivisions := mesh_nonneg_of_le hn hab
  let stepF : QInterval -> Nat -> QInterval := fun acc k =>
    let I := f.compute (rightPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  let stepR : QInterval -> Nat -> QInterval := fun acc k =>
    let I := (RealFunRaw.scaleRat r f).compute
      (rightPoint a b subdivisions k) prec
    { lo := acc.lo + mesh a b subdivisions * I.lo,
      hi := acc.hi + mesh a b subdivisions * I.hi }
  have hstep : forall k (A : QInterval),
      stepR (QInterval.scaleByRat r A) k =
        QInterval.scaleByRat r (stepF A k) := by
    intro k A
    dsimp [stepF, stepR, RealFunRaw.scaleRat,
      QInterval.scaleByRat]
    simp only [if_neg (by grind : ¬ 0 <= r)]
    grind [Rat.mul_assoc, Rat.mul_add, Rat.add_mul, Rat.mul_comm]
  have hfold : forall (xs : List Nat) (A : QInterval),
      xs.foldl stepR (QInterval.scaleByRat r A) =
        QInterval.scaleByRat r (xs.foldl stepF A) := by
    intro xs
    induction xs with
    | nil =>
        intro A
        rfl
    | cons k ks ih =>
        intro A
        simp only [List.foldl]
        rw [hstep k A]
        exact ih (stepF A k)
  have hzero : QInterval.scaleByRat r { lo := 0, hi := 0 } =
      { lo := 0, hi := 0 } := by
    simp [QInterval.scaleByRat]
  have h := hfold (List.range subdivisions) { lo := 0, hi := 0 }
  rw [hzero] at h
  simpa [stepF, stepR] using h

theorem QInterval.scaleByRat_add_mul_of_nonneg
    {r h : Rat} (hr : 0 <= r) (A I : QInterval) :
    QInterval.scaleByRat r
        { lo := A.lo + h * I.lo, hi := A.hi + h * I.hi } =
      { lo := (QInterval.scaleByRat r A).lo + (r * h) * I.lo,
        hi := (QInterval.scaleByRat r A).hi + (r * h) * I.hi } := by
  unfold QInterval.scaleByRat
  simp only [if_pos hr]
  grind [Rat.mul_assoc, Rat.mul_add]

theorem riemannLeftInterval_half_eq_half_scale_unit
    (g h : RealFunRaw) (subdivisions prec : Nat)
    (hpoint : forall k, k < subdivisions ->
      g.compute (leftPoint 0 ((1 : Rat) / 2) subdivisions k) prec =
        h.compute (leftPoint 0 1 subdivisions k) prec) :
    riemannLeftInterval g 0 ((1 : Rat) / 2) subdivisions prec =
      QInterval.scaleByRat (1 / 2)
        (riemannLeftInterval h 0 1 subdivisions prec) := by
  let stepG : QInterval -> Nat -> QInterval := fun acc k =>
    let I := g.compute (leftPoint 0 ((1 : Rat) / 2) subdivisions k) prec
    { lo := acc.lo + mesh 0 ((1 : Rat) / 2) subdivisions * I.lo,
      hi := acc.hi + mesh 0 ((1 : Rat) / 2) subdivisions * I.hi }
  let stepH : QInterval -> Nat -> QInterval := fun acc k =>
    let I := h.compute (leftPoint 0 1 subdivisions k) prec
    { lo := acc.lo + mesh 0 1 subdivisions * I.lo,
      hi := acc.hi + mesh 0 1 subdivisions * I.hi }
  have hstep : forall k, k < subdivisions -> forall A B,
      A = QInterval.scaleByRat (1 / 2) B ->
      stepG A k = QInterval.scaleByRat (1 / 2) (stepH B k) := by
    intro k hk A B hAB
    dsimp [stepG, stepH]
    rw [hpoint k hk, mesh_zero_half_eq_half_mesh_zero_one]
    rw [QInterval.scaleByRat_add_mul_of_nonneg
      (by decide +kernel : (0 : Rat) <= 1 / 2)]
    rw [hAB]
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < subdivisions) -> forall A B,
      A = QInterval.scaleByRat (1 / 2) B ->
      xs.foldl stepG A = QInterval.scaleByRat (1 / 2) (xs.foldl stepH B) := by
    intro xs
    induction xs with
    | nil =>
        intro _hmem A B hAB
        simpa using hAB
    | cons k ks ih =>
        intro hmem A B hAB
        simp only [List.foldl]
        apply ih (fun j hj => hmem j (by simp [hj]))
          (stepG A k) (stepH B k)
        exact hstep k (hmem k (by simp)) A B hAB
  simpa [riemannLeftInterval, stepG, stepH] using
    hfold (List.range subdivisions)
      (by intro k hk; exact List.mem_range.mp hk)
      { lo := 0, hi := 0 } { lo := 0, hi := 0 }
      (by simp [QInterval.scaleByRat])

/-- Effective modulus on a rational interval.

This is legacy pointwise-style continuity data used by the current FTC target.
Given an output precision `n`, it supplies:

* an input precision saying how close rational inputs must be;
* an evaluation precision saying how accurately to compute the function;
* a proof that sufficiently close inputs produce output intervals within the
  requested tolerance.

This is intentionally interval-based rather than topological. -/
structure EffectiveModulusOn (f : RealFunRaw) (a b : Rat) where
  valid : f.Valid
  inputPrecision : Nat -> Nat
  evalPrecision : Nat -> Nat
  close :
    forall x y n,
      a <= x ->
      x <= b ->
      a <= y ->
      y <= b ->
      qabs (y - x) <= (1 / ((inputPrecision n) : Rat)) ->
        intervalNearAtPrecision
          (f.compute x (evalPrecision n))
          (f.compute y (evalPrecision n))
          n

/- Constructive interval-sum integration.  The basic computation index is a
   stage number.  Higher-level constructors may use a tolerance to choose a
   sufficiently advanced stage, but tolerance selection is not part of the
   `RealCompute` foundation. -/
namespace Integral

/-- Effective choices for computing a sampled numerical candidate at a stage. -/
structure Plan where
  subdivisions : Nat
  evalPrecision : Nat

/-- The static dyadic mesh size used by the first sampling algorithms.
Stage `n` has `2^n` equal subintervals, independent of the integrand values. -/
def staticDyadicSubdivisions (n : Nat) : Nat :=
  2 ^ n

/-- The default static dyadic Riemann plan: stage `n` uses `2^n` equal
subintervals and asks the integrand for precision `n`. -/
def staticDyadicPlan : Nat -> Plan :=
  fun n => { subdivisions := staticDyadicSubdivisions n, evalPrecision := n }

/-- A rational Lipschitz estimate on the unit interval.  This is the finite
metric datum used by the elementary dyadic Riemann constructor below; it is
not a topological continuity assumption. -/
def LipschitzOnUnit (f : Rat -> Rat) (L : Rat) : Prop :=
  0 <= L /\
  forall s t : Rat,
    0 <= s -> s <= 1 -> 0 <= t -> t <= 1 ->
      qabs (f s - f t) <= L * qabs (t - s)

/-- A lower rectangle certified by a rational Lipschitz constant. -/
def lipschitzLowerCell (f : Rat -> Rat) (L p r : Rat) : Rat :=
  (r - p) * (f p - L * (r - p))

/-- The matching upper rectangle certified by a rational Lipschitz constant. -/
def lipschitzUpperCell (f : Rat -> Rat) (L p r : Rat) : Rat :=
  (r - p) * (f p + L * (r - p))

private theorem midpoint_left {p r : Rat} (hpr : p <= r) :
    p <= (p + r) / 2 := by
  apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
  · rw [Rat.div_def]
    calc
      p * 2 <= p + r := by grind
      _ = ((p + r) * (2 : Rat)⁻¹) * 2 := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · decide +kernel

private theorem midpoint_right {p r : Rat} (hpr : p <= r) :
    (p + r) / 2 <= r := by
  apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
  · rw [Rat.div_def]
    calc
      ((p + r) * (2 : Rat)⁻¹) * 2 = p + r := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= r * 2 := by grind
  · decide +kernel

private theorem midpoint_left_width (p r : Rat) :
    (p + r) / 2 - p = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem midpoint_right_width (p r : Rat) :
    r - (p + r) / 2 = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Splitting a unit-interval cell at its rational midpoint tightens the
Lipschitz bracket.  This is a purely finite inequality over rationals and is
the local refinement rule used by dyadic Riemann constructions. -/
theorem lipschitzCells_refine
    {f : Rat -> Rat} {L p r : Rat}
    (hlip : LipschitzOnUnit f L)
    (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    let q := (p + r) / 2
    lipschitzLowerCell f L p r <=
      lipschitzLowerCell f L p q + lipschitzLowerCell f L q r /\
    lipschitzUpperCell f L p q + lipschitzUpperCell f L q r <=
      lipschitzUpperCell f L p r := by
  intro q
  have hL0 := hlip.1
  have hpq : p <= q := by
    dsimp [q]
    exact midpoint_left hpr
  have hqr : q <= r := by
    dsimp [q]
    exact midpoint_right hpr
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hq1 : q <= 1 := Rat.le_trans hqr hr1
  have hpq_nonneg : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hqr_nonneg : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hqdist : qabs (q - p) = q - p :=
    qabs_eq_self_of_nonneg hpq_nonneg
  have hlip_pq := hlip.2 p q hp0 (Rat.le_trans hpr hr1) hq0 hq1
  have hforward : f p - f q <= L * (q - p) := by
    calc
      f p - f q <= qabs (f p - f q) := self_le_qabs _
      _ <= L * qabs (q - p) := hlip_pq
      _ = L * (q - p) := by rw [hqdist]
  have hreverse : f q - f p <= L * (q - p) := by
    calc
      f q - f p = -(f p - f q) := by
        grind [Rat.sub_eq_add_neg]
      _ <= qabs (-(f p - f q)) := self_le_qabs _
      _ = qabs (f p - f q) := qabs_neg _
      _ <= L * (q - p) := by simpa [hqdist] using hlip_pq
  have hleft_lower :
      f p - L * (r - p) <= f p - L * (q - p) := by
    have hwidth : q - p <= r - p := by grind [Rat.sub_eq_add_neg]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hwidth hL0
    grind [Rat.sub_eq_add_neg]
  have hright_lower :
      f p - L * (r - p) <= f q - L * (r - q) := by
    dsimp [q] at hforward ⊢
    rw [midpoint_right_width]
    grind [Rat.sub_eq_add_neg]
  have hleft_upper :
      f p + L * (q - p) <= f p + L * (r - p) := by
    have hwidth : q - p <= r - p := by grind [Rat.sub_eq_add_neg]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hwidth hL0
    grind [Rat.sub_eq_add_neg]
  have hright_upper :
      f q + L * (r - q) <= f p + L * (r - p) := by
    dsimp [q] at hreverse ⊢
    rw [midpoint_right_width]
    grind [Rat.sub_eq_add_neg]
  constructor
  · have hleft := Rat.mul_le_mul_of_nonneg_left hleft_lower hpq_nonneg
    have hright := Rat.mul_le_mul_of_nonneg_left hright_lower hqr_nonneg
    unfold lipschitzLowerCell
    calc
      (r - p) * (f p - L * (r - p)) =
          (q - p) * (f p - L * (r - p)) +
          (r - q) * (f p - L * (r - p)) := by
            grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
              Rat.add_assoc, Rat.add_comm]
      _ <= (q - p) * (f p - L * (q - p)) +
          (r - q) * (f q - L * (r - q)) :=
        rat_add_le_add hleft hright
  · have hleft := Rat.mul_le_mul_of_nonneg_left hleft_upper hpq_nonneg
    have hright := Rat.mul_le_mul_of_nonneg_left hright_upper hqr_nonneg
    unfold lipschitzUpperCell
    calc
      (q - p) * (f p + L * (q - p)) +
          (r - q) * (f q + L * (r - q)) <=
          (q - p) * (f p + L * (r - p)) +
          (r - q) * (f p + L * (r - p)) :=
        rat_add_le_add hleft hright
      _ = (r - p) * (f p + L * (r - p)) := by
        grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
          Rat.add_assoc, Rat.add_comm]

/-- A raw sampled-sum algorithm on a rational interval.

Given the requested output precision, choose a number of subintervals and an
evaluation precision, then compute the corresponding interval-valued left
sum. -/
structure Raw where
  integrand : RealFunRaw
  lower : Rat
  upper : Rat
  plan : Nat -> Plan

namespace Raw

def compute (I : Raw) (eps : Nat) : QInterval :=
  let p := I.plan eps
  riemannLeftInterval I.integrand I.lower I.upper p.subdivisions p.evalPrecision

def Valid (I : Raw) : Prop :=
  RealCompute.ValidCompute I.compute

def toRealCompute (I : Raw) (_h : I.Valid) : RealCompute where
  compute := I.compute

end Raw

/-- The certificate that an interval-valued sampled-sum algorithm is a
well-defined computable real number: boxes are ordered, nested, and their
widths shrink to zero. -/
structure Certificate (I : Raw) where
  width_nonneg : forall eps, 0 <= (I.compute eps).width
  nested :
    forall eps delta, eps <= delta ->
      (I.compute eps).lo <= (I.compute delta).lo /\
      (I.compute delta).lo <= (I.compute delta).hi /\
      (I.compute delta).hi <= (I.compute eps).hi
  widths_shrink : RealCompute.WidthsShrinkToZero I.compute

namespace Certificate

theorem valid {I : Raw} (cert : Certificate I) :
    I.Valid :=
  ⟨cert.width_nonneg, cert.nested, cert.widths_shrink⟩

def realCompute {I : Raw} (cert : Certificate I) : RealCompute :=
  I.toRealCompute cert.valid

end Certificate

/-- The interval-sum algorithm determined by a function, interval, and plan. -/
def algorithm (f : RealFunRaw) (a b : Rat) (plan : Nat -> Plan) :
    Raw where
  integrand := f
  lower := a
  upper := b
  plan := plan

/-- The unproved static-dyadic raw Riemann algorithm. Concrete numerical
constructions add the certificate proving that these dyadic boxes are ordered,
nested, and shrinking for the integrand at hand. -/
def staticDyadicAlgorithm (f : RealFunRaw) (a b : Rat) : Raw :=
  algorithm f a b staticDyadicPlan

/-- A sampled-sum computation with numerical validity. This does not prove
the mathematical integral role: even an exact singleton value from a fixed
coarse mesh can have a validity certificate. Use `Integral.HasIntegral` for
the semantic claim and `Integral.ConstructionFor` to package it. -/
structure SampleConstruction (f : RealFunRaw) (a b : Rat) where
  plan : Nat -> Plan
  certificate : Certificate (algorithm f a b plan)

/-- Extract the numerical candidate from a sampled-sum construction. -/
def sampleValue (f : RealFunRaw) (a b : Rat) (c : SampleConstruction f a b) : RealCompute :=
  Certificate.realCompute c.certificate

/-- Two sampled candidates with the same plan represent the same raw
value when their integrand enclosures agree at every finite sample read by
that plan.  This is the formal reason a dyadic-only special-function
evaluator can replace a general evaluator inside the equal-dyadic computation:
the replacement need not be defined by the same algorithm away from the
sample grid. -/
theorem integral_equiv_of_plan_and_samples
    {f g : RealFunRaw} {a b : Rat}
    (cf : SampleConstruction f a b) (cg : SampleConstruction g a b)
    (hplan : cf.plan = cg.plan)
    (hsamples : forall n k,
      k < (cf.plan n).subdivisions ->
      f.compute (leftPoint a b (cf.plan n).subdivisions k)
        (cf.plan n).evalPrecision =
        g.compute (leftPoint a b (cf.plan n).subdivisions k)
        (cf.plan n).evalPrecision) :
    (sampleValue f a b cf).Equiv (sampleValue g a b cg) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (sampleValue f a b cf) (sampleValue g a b cg) n n).2
  have hcompute :
      (sampleValue f a b cf).compute n =
        (sampleValue g a b cg).compute n := by
    unfold sampleValue Certificate.realCompute Raw.toRealCompute algorithm
    rw [← hplan]
    apply riemannLeftInterval_congr_of_samples
    intro k hk
    exact hsamples n k hk
  rw [hcompute]
  unfold QInterval.Overlaps
  have hwidth := cg.certificate.width_nonneg n
  change 0 <= ((sampleValue g a b cg).compute n).width at hwidth
  grind [QInterval.width]

/-- The interval-valued sample-transport theorem for equal-dyadic integrals.

Unlike `integral_equiv_of_plan_and_samples`, this version does not require
the two finite evaluators to return identical boxes.  Overlap at every point
read by the common plan is enough for overlap of the resulting rectangle sums.
This is the intended interface for replacing the arctangent-backed sine
evaluator by a separately implemented nested-radical evaluator. -/
theorem integral_equiv_of_plan_and_sample_overlaps
    {f g : RealFunRaw} {a b : Rat} (hab : a <= b)
    (cf : SampleConstruction f a b) (cg : SampleConstruction g a b)
    (hplan : cf.plan = cg.plan)
    (hsamples : forall n k,
      k < (cf.plan n).subdivisions ->
      QInterval.Overlaps
        (f.compute
          (leftPoint a b (cf.plan n).subdivisions k)
          (cf.plan n).evalPrecision)
        (g.compute
          (leftPoint a b (cf.plan n).subdivisions k)
          (cf.plan n).evalPrecision)) :
    (sampleValue f a b cf).Equiv (sampleValue g a b cg) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (sampleValue f a b cf) (sampleValue g a b cg) n n).2
  unfold sampleValue Certificate.realCompute Raw.toRealCompute algorithm
  rw [← hplan]
  exact riemannLeftInterval_overlap_of_samples f g a b hab
    (cf.plan n).subdivisions (cf.plan n).evalPrecision
    (fun k hk => hsamples n k hk)

/-- The exact constant integrand `x ↦ c`, as a raw function. -/
def constantFunRaw (c : Rat) : RealFunRaw :=
  RealFunRaw.exact (fun _ => c)

/-- The exact linear primitive `x ↦ c*x`, used for the constant-sampleValue
sanity check. -/
def linearPrimitiveFunRaw (c : Rat) : RealFunRaw :=
  RealFunRaw.exact (fun x => c * x)

/-- One-cell Riemann sums already compute constant integrands exactly. -/
def constantPlan : Nat -> Plan :=
  fun _ => { subdivisions := 1, evalPrecision := 0 }

theorem riemannLeftInterval_constant_one
    (c a b : Rat) (prec : Nat) :
    riemannLeftInterval (constantFunRaw c) a b 1 prec =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  unfold riemannLeftInterval constantFunRaw RealFunRaw.exact leftPoint mesh
  simp
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem constant_algorithm_compute
    (c a b : Rat) (n : Nat) :
    (algorithm (constantFunRaw c) a b constantPlan).compute n =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  simp [Raw.compute, algorithm, constantPlan]
  exact riemannLeftInterval_constant_one c a b 0

/-- The exact one-cell constant-integrand algorithm is a valid sampleValue
construction on every rational interval. -/
def constantConstruction (c a b : Rat) :
    SampleConstruction (constantFunRaw c) a b where
  plan := constantPlan
  certificate := by
    refine ⟨?_, ?_, ?_⟩
    · intro n
      rw [constant_algorithm_compute]
      simp [QInterval.width]
      grind [Rat.sub_eq_add_neg]
    · intro n m _hnm
      rw [constant_algorithm_compute, constant_algorithm_compute]
      simp
    · intro eps
      refine ⟨0, ?_⟩
      intro n _hn
      rw [constant_algorithm_compute]
      show (b - a) * c - (b - a) * c <= eps.val
      grind [Rat.sub_eq_add_neg]

theorem constantIntegral_compute
    (c a b : Rat) (n : Nat) :
    (sampleValue (constantFunRaw c) a b (constantConstruction c a b)).compute n =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  simp [sampleValue, Certificate.realCompute, Raw.toRealCompute, constantConstruction,
    constant_algorithm_compute]

theorem constantIntegral_valid (c a b : Rat) :
    (sampleValue (constantFunRaw c) a b (constantConstruction c a b)).Valid :=
  (constantConstruction c a b).certificate.valid

/-- Constant integrals respect pointwise addition. -/
theorem constantIntegral_add_equiv (c d a b : Rat) :
    (sampleValue (constantFunRaw (c + d)) a b
      (constantConstruction (c + d) a b)).Equiv
        { compute := RealCompute.addCompute
            (sampleValue (constantFunRaw c) a b
              (constantConstruction c a b))
            (sampleValue (constantFunRaw d) a b
              (constantConstruction d a b)) } := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((sampleValue (constantFunRaw (c + d)) a b
      (constantConstruction (c + d) a b)).compute n)
    (RealCompute.addCompute
      (sampleValue (constantFunRaw c) a b (constantConstruction c a b))
      (sampleValue (constantFunRaw d) a b (constantConstruction d a b)) n)
  rw [constantIntegral_compute]
  unfold RealCompute.addCompute
  rw [constantIntegral_compute c a b n, constantIntegral_compute d a b n]
  unfold QInterval.Overlaps
  constructor <;>
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]

/-- Constant integrals respect rational scalar multiplication. -/
theorem constantIntegral_scaleRat_equiv (r c a b : Rat) :
    (sampleValue (constantFunRaw (r * c)) a b
      (constantConstruction (r * c) a b)).Equiv
        { compute := RealCompute.scaleRatCompute r
            (sampleValue (constantFunRaw c) a b
              (constantConstruction c a b)) } := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((sampleValue (constantFunRaw (r * c)) a b
      (constantConstruction (r * c) a b)).compute n)
    (RealCompute.scaleRatCompute r
      (sampleValue (constantFunRaw c) a b (constantConstruction c a b)) n)
  rw [constantIntegral_compute]
  unfold RealCompute.scaleRatCompute
  rw [constantIntegral_compute c a b n]
  unfold QInterval.Overlaps
  by_cases hr : 0 <= r
  · simp [hr]
    constructor <;>
      grind [Rat.mul_assoc, Rat.mul_comm]
  · simp [hr]
    constructor <;>
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Constant integrals are additive on adjacent rational intervals. -/
theorem constantIntegral_adjacent_additive (k a b c : Rat) :
    (sampleValue (constantFunRaw k) a c
      (constantConstruction k a c)).Equiv
        { compute := RealCompute.addCompute
            (sampleValue (constantFunRaw k) a b
              (constantConstruction k a b))
            (sampleValue (constantFunRaw k) b c
              (constantConstruction k b c)) } := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((sampleValue (constantFunRaw k) a c
      (constantConstruction k a c)).compute n)
    (RealCompute.addCompute
      (sampleValue (constantFunRaw k) a b (constantConstruction k a b))
      (sampleValue (constantFunRaw k) b c (constantConstruction k b c)) n)
  rw [constantIntegral_compute]
  unfold RealCompute.addCompute
  rw [constantIntegral_compute k a b n, constantIntegral_compute k b c n]
  unfold QInterval.Overlaps
  constructor <;>
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]


end Integral

/-- Existence of a valid sampled numerical candidate. This is deliberately
weaker than existence of an integral: no semantic range or approximation
condition is asserted. Mathematical existence means a `HasIntegral` witness. -/
def Integral.ExistsSampleConstruction (f : RealFunRaw) (a b : Rat) : Prop :=
  Nonempty (Integral.SampleConstruction f a b)

def endpointDifferenceInterval (F : RealFunRaw) (a b : Rat) (prec : Nat) : QInterval :=
  let A := F.compute a prec
  let B := F.compute b prec
  { lo := B.lo - A.hi, hi := B.hi - A.lo }

/-- The width of an endpoint-difference box is exactly the sum of the two
endpoint evaluation widths. -/
theorem endpointDifferenceInterval_width (F : RealFunRaw) (a b : Rat)
    (prec : Nat) :
    (endpointDifferenceInterval F a b prec).width =
      (F.compute a prec).width + (F.compute b prec).width := by
  unfold endpointDifferenceInterval QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- A valid primitive produces an ordered endpoint-difference enclosure at
every finite computation stage. -/
theorem endpointDifferenceInterval_width_nonneg {F : RealFunRaw}
    (hF : F.Valid) {a b : Rat} (ha : F.domain a) (hb : F.domain b)
    (prec : Nat) :
    0 <= (endpointDifferenceInterval F a b prec).width := by
  rw [endpointDifferenceInterval_width]
  exact Rat.add_nonneg ((hF a ha).1 prec) ((hF b hb).1 prec)

def endpointDifferenceCompute (F : RealFunRaw) (a b : Rat) : Nat -> QInterval :=
  fun prec => endpointDifferenceInterval F a b prec

/-- At one fixed evaluation stage, adjacent endpoint-difference enclosures
combine to enclose the endpoint difference across both cells.  The only loss
comes from the (nonnegative) width of the shared middle evaluation box. -/
theorem endpointDifferenceInterval_adjacent_additive_contains
    {F : RealFunRaw} {a b c : Rat} {prec : Nat}
    (hmiddle : 0 <= (F.compute b prec).width) :
    QInterval.ContainsInterval
      (QInterval.addInterval
        (endpointDifferenceInterval F a b prec)
        (endpointDifferenceInterval F b c prec))
      (endpointDifferenceInterval F a c prec) := by
  unfold endpointDifferenceInterval QInterval.addInterval QInterval.ContainsInterval
    QInterval.width at *
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

def endpointDifferenceRaw (F : RealFunRaw) (a b : Rat)
    (_h : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) : RealCompute where
  compute := endpointDifferenceCompute F a b

/-- Endpoint differences are valid whenever the primitive is valid at both
endpoints. -/
theorem endpointDifference_valid_of_fun_valid
    {F : RealFunRaw} (hF : F.Valid) {a b : Rat}
    (ha : F.domain a) (hb : F.domain b) :
    RealCompute.ValidCompute (endpointDifferenceCompute F a b) := by
  let A : RealCompute := F.apply hF a ha
  let B : RealCompute := F.apply hF b hb
  have hA : A.Valid := by
    simpa [A, RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hB : B.Valid := by
    simpa [B, RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hsub := RealCompute.subCompute_valid hB hA
  change RealCompute.ValidCompute (RealCompute.subCompute B A) at hsub
  change RealCompute.ValidCompute (RealCompute.subCompute B A)
  exact hsub

/-! The interval implementation of an endpoint difference is the same raw
real as subtracting the two endpoint evaluations.  This is the small API
bridge that lets an effective FTC certificate state its conclusion using the
familiar notation `F b - F a`. -/

theorem endpointDifferenceRaw_equiv_sub_apply
    {F : RealFunRaw} (hF : F.Valid) {a b : Rat}
    (ha : F.domain a) (hb : F.domain b)
    (hdiff : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    (endpointDifferenceRaw F a b hdiff).Equiv
      ((F.apply hF b hb) - (F.apply hF a ha)) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (endpointDifferenceRaw F a b hdiff)
    ((F.apply hF b hb) - (F.apply hF a ha)) n n).2
  change QInterval.Overlaps
    (endpointDifferenceInterval F a b n)
    (RealCompute.subCompute (F.apply hF b hb) (F.apply hF a ha) n)
  unfold endpointDifferenceInterval RealCompute.subCompute
    RealFunRaw.apply RealFunRaw.applyCompute
  simp only [QInterval.Overlaps]
  have hAvalid : (F.apply hF a ha).Valid := by
    simpa [RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hBvalid : (F.apply hF b hb).Valid := by
    simpa [RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hA := RealCompute.interval_order_of_valid (F.apply hF a ha) hAvalid n
  have hB := RealCompute.interval_order_of_valid (F.apply hF b hb) hBvalid n
  change (F.compute a n).lo <= (F.compute a n).hi at hA
  change (F.compute b n).lo <= (F.compute b n).hi at hB
  grind

/-- Endpoint differences telescope over adjacent intervals:
\((F(b)-F(a))+(F(c)-F(b))\sim F(c)-F(a)\). -/
theorem endpointDifferenceRaw_adjacent_additive
    {F : RealFunRaw} (hF : F.Valid) {a b c : Rat}
    (ha : F.domain a) (hb : F.domain b) (hc : F.domain c)
    (hab : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (hbc : RealCompute.ValidCompute (endpointDifferenceCompute F b c))
    (hac : RealCompute.ValidCompute (endpointDifferenceCompute F a c)) :
    ((endpointDifferenceRaw F a b hab) +
      (endpointDifferenceRaw F b c hbc)).Equiv
        (endpointDifferenceRaw F a c hac) := by
  let A : RealCompute := F.apply hF a ha
  let B : RealCompute := F.apply hF b hb
  let C : RealCompute := F.apply hF c hc
  have hA : A.Valid := by
    simpa [A, RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hB : B.Valid := by
    simpa [B, RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hC : C.Valid := by
    simpa [C, RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF c hc
  change (B - A + (C - B)).Equiv (C - A)
  exact RealCompute.sub_add_sub_cancel_middle_equiv hA hB hC

/-- Numerical agreement between a sampled candidate and an endpoint difference.
The semantic integral role is separate (`Integral.HasIntegral`).

Equality of computable reals is `RealCompute.Equiv`: at every common computation stage,
the two rational intervals overlap. -/
def CandidateEqualsEndpointDifference
    (F dF : RealFunRaw) (a b : Rat)
    (c : Integral.SampleConstruction dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) : Prop :=
  (Integral.sampleValue dF a b c).Equiv
    (endpointDifferenceRaw F a b hendpoint)

/-- Scheduled numerical comparison between sample sums and endpoint boxes.
This is construction data, not the mathematical FTC specification. To use
its numerical result as an integral, establish `Integral.HasIntegral`; the
general conditional FTC theorem lives in `IntegralFTC`. -/
structure EffectiveFTC (F dF : RealFunRaw) (a b : Rat) where
  chooseN : QPos -> Nat
  chooseEvalPrecision : QPos -> Nat
  good : forall eps,
    QInterval.CloseAt
      (riemannLeftInterval dF a b (chooseN eps) (chooseEvalPrecision eps))
      (endpointDifferenceInterval F a b (chooseEvalPrecision eps))
      eps

/-- Static-dyadic specialization of `EffectiveFTC`.

This is the certificate shape for the first bounded-integral algorithms:
for each requested rational precision choose a dyadic stage `s`, use
`2^s` equal subintervals of `[a,b]`, and compare the resulting left-Riemann
interval with the endpoint-difference interval. -/
structure StaticDyadicEffectiveFTC (F dF : RealFunRaw) (a b : Rat) where
  chooseStage : QPos -> Nat
  chooseEvalPrecision : QPos -> Nat
  good : forall eps,
    QInterval.CloseAt
      (riemannLeftInterval dF a b
        (Integral.staticDyadicSubdivisions (chooseStage eps))
        (chooseEvalPrecision eps))
      (endpointDifferenceInterval F a b (chooseEvalPrecision eps))
      eps

namespace StaticDyadicEffectiveFTC

/-- Forget that the subdivisions were chosen by the static dyadic mesh. -/
def toEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) :
    EffectiveFTC F dF a b where
  chooseN := fun eps => Integral.staticDyadicSubdivisions (h.chooseStage eps)
  chooseEvalPrecision := h.chooseEvalPrecision
  good := h.good

end StaticDyadicEffectiveFTC

def ftcErrorExact (F dF : Rat -> Rat) (a b : Rat) (n : Nat) : Rat :=
  qabs (riemannLeftExact dF a b n - (F b - F a))

def ftcCheckExact (F dF : Rat -> Rat) (a b tolerance : Rat) (n : Nat) : Bool :=
  decide (ftcErrorExact F dF a b n <= tolerance)

/-- Exact rational-function FTC data.

The hypothesis is explicit: `dF` is an effective derivative of `F`.  The
conclusion is the definite-integral statement: for every positive rational
precision, a finite left sum for `dF` over `[a,b]` is within that precision of
`F(b)-F(a)`. -/
structure EffectiveFTCExact (F dF : Rat -> Rat) (a b : Rat) where
  derivative : EffectiveDerivativeExact F dF
  chooseN : QPos -> Nat
  good : forall eps, ftcErrorExact F dF a b (chooseN eps) <= eps.val

/-! The exact constant rectangle sum is the finite algebra behind the first
end-to-end FTC instance.  No refinement or real-number completion is needed:
one positive cell already has the exact width-times-height value. -/
theorem riemannLeftExact_constant_one (c a b : Rat) :
    riemannLeftExact (fun _ => c) a b 1 = (b - a) * c := by
  unfold riemannLeftExact mesh leftPoint
  simp
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-! A finite arithmetic lemma for affine rectangle heights.  It is the only
summation fact needed for the first nonlinear FTC example; the index sum is
proved by induction over `List.range`, not by invoking an infinite series. -/
private theorem foldl_affine_range (h a d : Rat) (n : Nat) :
    (List.range n : List Nat).foldl
      (fun acc (k : Nat) => acc + h * (a + (k : Rat) * d)) 0 =
      (n : Rat) * h * a +
        h * d * (((n : Rat) * ((n : Rat) - 1)) / 2) := by
  induction n with
  | zero => simp <;> grind [Rat.div_def]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      simp only [Rat.natCast_add]
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
        Rat.mul_assoc, Rat.mul_comm]

/-! Every finite affine rectangle sum has a closed rational form.  Keeping the
mesh explicit makes this theorem valid even at stage zero; the positive-stage
normalization `n * mesh = b - a` can be applied separately when an integral
error bound is needed. -/
theorem riemannLeftExact_affine_closed
    (r c a b : Rat) (n : Nat) :
    riemannLeftExact (fun x => r * x + c) a b n =
      (n : Rat) * mesh a b n * (r * a + c) +
        mesh a b n * (r * mesh a b n) *
          (((n : Rat) * ((n : Rat) - 1)) / 2) := by
  unfold riemannLeftExact
  dsimp
  unfold leftPoint
  have hrewrite :
      (fun acc (k : Nat) =>
          acc + mesh a b n * (r * (a + (k : Rat) * mesh a b n) + c)) =
        (fun acc (k : Nat) =>
          acc + mesh a b n *
            ((r * a + c) + (k : Rat) * (r * mesh a b n))) := by
    funext acc k
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
      Rat.add_assoc, Rat.add_comm]
  rw [hrewrite, foldl_affine_range]

/-! After normalizing a positive mesh, the affine rectangle error is an
explicit rational term.  Thus the affine FTC does not need a completeness
argument: the error budget is visible at every finite stage. -/
theorem riemannLeftExact_affine_error_of_pos
    {r c a b : Rat} {n : Nat} (hn : 0 < n) :
    riemannLeftExact (fun x => r * x + c) a b n =
      (b - a) * (r * (a + b) / 2 + c) -
        r * (b - a) ^ 2 / (2 * (n : Rat)) := by
  rw [riemannLeftExact_affine_closed]
  have htotal := natCast_mul_mesh_eq_sub (a := a) (b := b) hn
  have hmesh : (n : Rat) * mesh a b n = b - a := htotal
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm,
    Rat.mul_inv_cancel]

theorem riemannLeftExact_doubleId_of_pos {a b : Rat} {n : Nat}
    (hn : 0 < n) :
    riemannLeftExact (fun x => 2 * x) a b n =
      (b ^ 2 - a ^ 2) - (b - a) ^ 2 / (n : Rat) := by
  let h : Rat := mesh a b n
  have hmesh : h = (b - a) / (n : Rat) := by
    dsimp [h, mesh]
    rw [if_neg (Nat.ne_of_gt hn)]
  have hfold := foldl_affine_range h (2 * a) (2 * h) n
  unfold riemannLeftExact
  dsimp
  simp only [mesh, if_neg (Nat.ne_of_gt hn)]
  rw [← hmesh]
  unfold leftPoint
  change (List.range n).foldl
      (fun acc (k : Nat) => acc + h * (2 * (a + (k : Rat) * h))) 0 = _
  have hrewrite :
      (fun acc (k : Nat) => acc + h * (2 * (a + (k : Rat) * h))) =
        (fun acc (k : Nat) => acc + h * ((2 * a) + (k : Rat) * (2 * h))) := by
    funext acc k
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  rw [hrewrite, hfold]
  have htotal := natCast_mul_mesh_eq_sub (a := a) (b := b) hn
  have htotal' : (n : Rat) * h = b - a := by
    simpa [h] using htotal
  change (n : Rat) * h * (2 * a) +
      h * (2 * h) * ((n : Rat) * ((n : Rat) - 1) / 2) = _
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.div_def,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_add, Rat.add_mul]

/-! The next polynomial case uses the finite sum of squares.  This is kept as
an explicit induction over `List.range`: it is a finite certificate used by
the cubic FTC instance, not an appeal to an infinite series. -/
private theorem foldl_square_range (h : Rat) (n : Nat) :
    (List.range n : List Nat).foldl
      (fun acc (k : Nat) => acc + h * (k : Rat) ^ 2) 0 =
      h * (((n : Rat) * ((n : Rat) - 1) *
        (2 * (n : Rat) - 1)) / 6) := by
  induction n with
  | zero =>
      simp
      grind [Rat.sub_eq_add_neg, Rat.div_def]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      simp only [Rat.natCast_add]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.pow_succ,
        Rat.div_def]

theorem riemannLeftExact_threeSquare_unit_of_pos {n : Nat} (hn : 0 < n) :
    riemannLeftExact (fun x => 3 * x ^ 2) 0 1 n =
      3 * (1 / (n : Rat)) ^ 3 *
        (((n : Rat) * ((n : Rat) - 1) *
          (2 * (n : Rat) - 1)) / 6) := by
  let h : Rat := mesh 0 1 n
  have hmesh' : mesh 0 1 n = 1 / (n : Rat) := by
    dsimp [mesh]
    rw [if_neg (Nat.ne_of_gt hn)]
    grind [Rat.sub_eq_add_neg]
  have hmesh : h = 1 / (n : Rat) := by
    dsimp [h]
    exact hmesh'
  unfold riemannLeftExact
  dsimp
  unfold leftPoint
  rw [hmesh', ← hmesh]
  simp only [Rat.zero_add]
  change (List.range n).foldl
      (fun acc (k : Nat) => acc + h * (3 * ((k : Rat) * h) ^ 2)) 0 = _
  have hrewrite :
      (fun acc (k : Nat) => acc + h * (3 * ((k : Rat) * h) ^ 2)) =
        (fun acc (k : Nat) => acc + (3 * h ^ 3) * (k : Rat) ^ 2) := by
    funext acc k
    grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm]
  rw [hrewrite, foldl_square_range]

def inDomainInterval (a b x : Rat) : Prop :=
  a <= x /\ x <= b

def subintervalOf (I : QInterval) (a b : Rat) : Prop :=
  a <= I.lo /\ I.lo <= I.hi /\ I.hi <= b

/-- A rational closed subinterval of a rational closed interval.  This is the
piece size used by the convex/concave calculus certificates below. -/
structure RationalSubinterval (a b : Rat) where
  lower : Rat
  upper : Rat
  lower_mem : a <= lower
  ordered : lower <= upper
  upper_mem : upper <= b

namespace RationalSubinterval

def contains {a b : Rat} (C : RationalSubinterval a b) (x : Rat) : Prop :=
  C.lower <= x /\ x <= C.upper

theorem contains_inDomain {a b : Rat} (C : RationalSubinterval a b)
    {x : Rat} (hx : C.contains x) :
    inDomainInterval a b x :=
  And.intro
    (Rat.le_trans C.lower_mem hx.1)
    (Rat.le_trans hx.2 C.upper_mem)

def whole (a b : Rat) (hab : a <= b) : RationalSubinterval a b where
  lower := a
  upper := b
  lower_mem := Rat.le_refl
  ordered := hab
  upper_mem := Rat.le_refl

def width {a b : Rat} (C : RationalSubinterval a b) : Rat :=
  C.upper - C.lower

def scaleBound {a b : Rat} (C : RationalSubinterval a b)
    (B : QInterval) : QInterval :=
  QInterval.scaleByRat C.width B

end RationalSubinterval

/-- A finite rational partition of `[a,b]`, represented by monotone rational
grid points.  The cells are the short intervals on which derivative bounds are
certified. -/
structure RationalPartition (a b : Rat) where
  pieces : Nat
  positive : 0 < pieces
  point : Nat -> Rat
  left_endpoint : point 0 = a
  right_endpoint : point pieces = b
  monotone :
    forall i j, i <= j -> j <= pieces -> point i <= point j

namespace RationalPartition

/-- The explicit equally-spaced rational partition of an ordered interval.
Uniform partitions are the first common-refinement interface needed for the
geometric integration-by-parts route: multiplication of the number of pieces
gives a single rational grid containing both input grids. -/
def uniform (a b : Rat) (pieces : Nat)
    (hpieces : 0 < pieces) (hab : a <= b) : RationalPartition a b where
  pieces := pieces
  positive := hpieces
  point := leftPoint a b pieces
  left_endpoint := leftPoint_zero a b pieces
  right_endpoint := leftPoint_endpoint hpieces
  monotone := by
    intro i j hij _hj
    exact leftPoint_monotone hpieces hab hij

/-- The old indices of the `m`-piece uniform grid remain valid in its
`m*n`-piece refinement. -/
theorem uniform_refinement_index_right {m n i : Nat}
    (hi : i <= m) : i * n <= m * n :=
  Nat.mul_le_mul_right n hi

/-- The old indices of the `n`-piece uniform grid remain valid in the common
`m*n` refinement. -/
theorem uniform_refinement_index_left {m n j : Nat}
    (hj : j <= n) : j * m <= m * n := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right m hj

/-- The `m*n` uniform grid contains the complete `m`-piece grid. -/
theorem uniform_refines_right {a b : Rat} {m n i : Nat}
    (hm : 0 < m) (hn : 0 < n) (hab : a <= b) :
    (uniform a b (m * n) (Nat.mul_pos hm hn) hab).point (i * n) =
      (uniform a b m hm hab).point i := by
  simpa [uniform] using leftPoint_refine_mul_right
    (a := a) (b := b) (i := i) hm hn

/-- The `m*n` uniform grid contains the complete `n`-piece grid as well.
Together with `uniform_refines_right` this is an explicit common rational
refinement, not a choice principle over arbitrary partitions. -/
theorem uniform_refines_left {a b : Rat} {m n j : Nat}
    (hm : 0 < m) (hn : 0 < n) (hab : a <= b) :
    (uniform a b (m * n) (Nat.mul_pos hm hn) hab).point (j * m) =
      (uniform a b n hn hab).point j := by
  simpa [uniform, Nat.mul_comm] using leftPoint_refine_mul_right
    (a := a) (b := b) (i := j) hn hm

/-- A finite rational partition `fine` refines `coarse` when it explicitly
embeds every coarse grid point into the fine grid, preserving endpoints and
index order.  This is finite data: no supremum, density, or completed real
line is involved. -/
structure Refines {a b : Rat}
    (fine coarse : RationalPartition a b) where
  index : Nat -> Nat
  index_zero : index 0 = 0
  index_last : index coarse.pieces = fine.pieces
  index_mono : forall i j, i <= j -> index i <= index j
  point_eq : forall i, i <= coarse.pieces ->
    fine.point (index i) = coarse.point i

/-- Every embedded coarse index is a valid index in the refining partition. -/
theorem Refines.index_le {a b : Rat}
    {fine coarse : RationalPartition a b} (R : Refines fine coarse)
    {i : Nat} (hi : i <= coarse.pieces) :
    R.index i <= fine.pieces := by
  calc
    R.index i <= R.index coarse.pieces := R.index_mono i coarse.pieces hi
    _ = fine.pieces := R.index_last

/-- Every fine breakpoint between two consecutive embedded coarse indices lies
in the corresponding coarse cell.  This is the finite order fact needed to
transfer a cellwise derivative, monotonicity, or variation bound to a common
refinement. -/
theorem Refines.point_between_consecutive {a b : Rat}
    {fine coarse : RationalPartition a b} (R : Refines fine coarse)
    {i j : Nat} (hi : i < coarse.pieces)
    (hleft : R.index i <= j) (hright : j <= R.index (i + 1)) :
    coarse.point i <= fine.point j /\ fine.point j <= coarse.point (i + 1) := by
  have hisucc : i + 1 <= coarse.pieces := Nat.succ_le_of_lt hi
  have hjfine : j <= fine.pieces :=
    Nat.le_trans hright (R.index_le hisucc)
  constructor
  · calc
      coarse.point i = fine.point (R.index i) := (R.point_eq i (Nat.le_of_lt hi)).symm
      _ <= fine.point j := fine.monotone _ _ hleft hjfine
  · calc
      fine.point j <= fine.point (R.index (i + 1)) :=
        fine.monotone _ _ hright (R.index_le hisucc)
      _ = coarse.point (i + 1) := R.point_eq _ hisucc

/-- Every partition refines itself by the identity index map. -/
def Refines.refl {a b : Rat} (P : RationalPartition a b) : Refines P P where
  index := fun i => i
  index_zero := rfl
  index_last := rfl
  index_mono := by
    intro i j hij
    exact hij
  point_eq := by
    intro i _hi
    rfl

/-- Finite refinement certificates compose.  This lets a later construction
refine a mesh in several explicit rational stages without losing the map back
to its original partition. -/
def Refines.trans {a b : Rat}
    {fine middle coarse : RationalPartition a b}
    (Rfine : Refines fine middle) (Rmiddle : Refines middle coarse) :
    Refines fine coarse where
  index := fun i => Rfine.index (Rmiddle.index i)
  index_zero := by
    rw [Rmiddle.index_zero, Rfine.index_zero]
  index_last := by
    rw [Rmiddle.index_last, Rfine.index_last]
  index_mono := by
    intro i j hij
    exact Rfine.index_mono _ _ (Rmiddle.index_mono i j hij)
  point_eq := by
    intro i hi
    calc
      fine.point (Rfine.index (Rmiddle.index i)) =
          middle.point (Rmiddle.index i) :=
        Rfine.point_eq _ (Rmiddle.index_le hi)
      _ = coarse.point i := Rmiddle.point_eq i hi

/-- A common rational refinement carries one finite refinement certificate for
each input grid. -/
structure CommonRefinement {a b : Rat}
    (left right : RationalPartition a b) where
  refinement : RationalPartition a b
  refines_left : Refines refinement left
  refines_right : Refines refinement right

/-- The `m*n` uniform grid is a certified common refinement of the `m` and
`n` grids.  Its two embeddings are the elementary index multiplications
`i ↦ i*n` and `j ↦ j*m`. -/
def uniformCommonRefinement (a b : Rat) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hab : a <= b) :
    CommonRefinement (uniform a b m hm hab) (uniform a b n hn hab) where
  refinement := uniform a b (m * n) (Nat.mul_pos hm hn) hab
  refines_left :=
    { index := fun i => i * n
      index_zero := by grind
      index_last := by simp [uniform]
      index_mono := by
        intro i j hij
        exact Nat.mul_le_mul_right n hij
      point_eq := by
        intro i _hi
        exact uniform_refines_right hm hn hab }
  refines_right :=
    { index := fun j => j * m
      index_zero := by grind
      index_last := by simp [uniform, Nat.mul_comm]
      index_mono := by
        intro i j hij
        exact Nat.mul_le_mul_right m hij
      point_eq := by
        intro j _hj
        exact uniform_refines_left hm hn hab }

/-- Insert one rational breakpoint after cell index `k`.  The new list keeps
all old points in order, placing `x` between `point k` and `point (k+1)`.
Repeated use of this finite operation is the constructive route from explicit
breakpoint lists to a general common refinement. -/
def insertPointValue {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (x : Rat) : Nat -> Rat :=
  fun i => if i <= k then P.point i else
    if i = k + 1 then x else P.point (i - 1)

/-- Scan a finite breakpoint list from the left for a cell whose right
endpoint reaches a specified rational value.  The fuel is explicit so this is
a total rational computation, not a choice of a supremum. -/
def locateInsertionCellAux {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (i fuel : Nat) : Nat :=
  match fuel with
  | 0 => i
  | fuel + 1 =>
      if x <= P.point (i + 1) then i
      else locateInsertionCellAux P x (i + 1) fuel

/-- Locate a cell containing `x` by scanning all cells of a finite rational
partition.  Its correctness proof below supplies the local ordering data for
the subsequent insertion. -/
def locateInsertionCell {a b : Rat} (P : RationalPartition a b)
    (x : Rat) : Nat :=
  locateInsertionCellAux P x 0 P.pieces

/-- Correctness of the finite left-to-right cell scan. -/
theorem locateInsertionCellAux_spec {a b : Rat} (P : RationalPartition a b)
    (x : Rat) :
    forall (i fuel : Nat),
      0 < fuel ->
      i + fuel <= P.pieces ->
      P.point i <= x ->
      x <= P.point (i + fuel) ->
      let k := locateInsertionCellAux P x i fuel
      i <= k /\ k < i + fuel /\ P.point k <= x /\ x <= P.point (k + 1) := by
  intro i fuel hfuel hbound hleft hright
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
      simp only [locateInsertionCellAux]
      by_cases hnext : x <= P.point (i + 1)
      · rw [if_pos hnext]
        exact ⟨Nat.le_refl _, by omega, hleft, hnext⟩
      · rw [if_neg hnext]
        cases fuel with
        | zero =>
            exfalso
            apply hnext
            simpa using hright
        | succ fuel =>
            have hnext_left : P.point (i + 1) <= x := by
              exact (Rat.le_total : P.point (i + 1) <= x \/ x <= P.point (i + 1)).resolve_right hnext
            have hbound' : (i + 1) + (fuel + 1) <= P.pieces := by omega
            have hright' : x <= P.point ((i + 1) + (fuel + 1)) := by
              have hindex : (i + 1) + (fuel + 1) = i + (fuel + 1 + 1) := by omega
              simpa [hindex] using hright
            rcases ih (i + 1) (by omega) hbound' hnext_left hright' with
              ⟨hfirst, hsecond, hvalue, hupper⟩
            exact ⟨Nat.le_trans (Nat.le_succ i) hfirst, by omega, hvalue, hupper⟩

/-- A point in the enclosing interval is located in an actual partition cell,
with all bounds obtained by the finite scan. -/
theorem locateInsertionCell_spec {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) :
    locateInsertionCell P x < P.pieces /\
      P.point (locateInsertionCell P x) <= x /\
      x <= P.point (locateInsertionCell P x + 1) := by
  have h := locateInsertionCellAux_spec P x 0 P.pieces P.positive
    (by omega) (by simpa [P.left_endpoint] using hleft)
    (by simpa [P.right_endpoint] using hright)
  simpa [locateInsertionCell] using h

/-- The partition obtained by inserting a rational point in one specified
cell.  Degenerate insertion at an endpoint is allowed: partitions record
monotone, rather than strictly increasing, rational breakpoint data. -/
def insertPoint {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) (x : Rat)
    (hleft : P.point k <= x) (hright : x <= P.point (k + 1)) :
    RationalPartition a b where
  pieces := P.pieces + 1
  positive := by omega
  point := insertPointValue P k x
  left_endpoint := by
    simp [insertPointValue, P.left_endpoint]
  right_endpoint := by
    have hnot : ¬ (P.pieces + 1 <= k) := by omega
    have hneq : P.pieces ≠ k := by omega
    simp [insertPointValue, hnot, hneq, P.right_endpoint]
  monotone := by
    intro i j hij hj
    by_cases hjk : j <= k
    · have hik : i <= k := Nat.le_trans hij hjk
      simp [insertPointValue, hik, hjk]
      exact P.monotone i j hij (Nat.le_trans hjk (Nat.le_of_lt hk))
    · have hkj : k + 1 <= j := by omega
      by_cases hik : i <= k
      · by_cases hjeq : j = k + 1
        · subst j
          simp [insertPointValue, hik, hjk]
          exact Rat.le_trans
            (P.monotone i k hik (Nat.le_of_lt hk)) hleft
        · have hsub : j - 1 <= P.pieces := by omega
          have hisub : i <= j - 1 := by omega
          simp [insertPointValue, hik, hjk, hjeq]
          exact P.monotone i (j - 1) hisub hsub
      · have hki : k + 1 <= i := by omega
        by_cases hieq : i = k + 1
        · subst i
          by_cases hjeq : j = k + 1
          · subst j
            simp [insertPointValue, hjk]
          · have hsub : j - 1 <= P.pieces := by omega
            have hbetween : k + 1 <= j - 1 := by omega
            have hnotik : ¬ (k + 1 <= k) := by omega
            simp [insertPointValue, hjk, hjeq, hnotik]
            exact Rat.le_trans hright (P.monotone (k + 1) (j - 1) hbetween hsub)
        · have hsubi : i - 1 <= P.pieces := by omega
          have hsubj : j - 1 <= P.pieces := by omega
          have hisub : i - 1 <= j - 1 := by omega
          have hjeq : j ≠ k + 1 := by omega
          simp [insertPointValue, hik, hjk, hieq, hjeq]
          exact P.monotone (i - 1) (j - 1) hisub hsubj

/-- Insert a rational point known to lie in the enclosing interval, choosing
its containing cell by the explicit finite scan. -/
def insertLocatedPoint {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) : RationalPartition a b :=
  let h := locateInsertionCell_spec P x hleft hright
  insertPoint P (locateInsertionCell P x) h.1 x h.2.1 h.2.2

/-- The old partition is explicitly embedded in a one-point insertion. -/
def insertPoint_refines {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) (x : Rat)
    (hleft : P.point k <= x) (hright : x <= P.point (k + 1)) :
    Refines (insertPoint P k hk x hleft hright) P where
  index := fun i => if i <= k then i else i + 1
  index_zero := by simp
  index_last := by
    have hnot : ¬ (P.pieces <= k) := by omega
    simp [hnot, insertPoint]
  index_mono := by
    intro i j hij
    by_cases hik : i <= k
    · by_cases hjk : j <= k
      · simp [hik, hjk, hij]
      · have hle : i <= j + 1 := by omega
        simp [hik, hjk, hle]
    · have hjk : ¬ j <= k := by
        intro hjk
        exact hik (Nat.le_trans hij hjk)
      have hle : i + 1 <= j + 1 := Nat.succ_le_succ hij
      simp [hik, hjk, hle]
  point_eq := by
    intro i hi
    by_cases hik : i <= k
    · simp [insertPoint, insertPointValue, hik]
    · have hindex : ¬ (i + 1 <= k) := by omega
      have hneq : i ≠ k := by omega
      simp [insertPoint, insertPointValue, hik, hindex, hneq]

/-- The scan-selected insertion is also a certified refinement of the old
partition. -/
def insertLocatedPoint_refines {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) :
    Refines (insertLocatedPoint P x hleft hright) P := by
  unfold insertLocatedPoint
  dsimp
  exact insertPoint_refines _ _ _ _ _ _

/-- A single arbitrary rational breakpoint yields a certified common
refinement of the old partition and the inserted partition. -/
def insertPointCommonRefinement {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) (x : Rat)
    (hleft : P.point k <= x) (hright : x <= P.point (k + 1)) :
    CommonRefinement P (insertPoint P k hk x hleft hright) where
  refinement := insertPoint P k hk x hleft hright
  refines_left := insertPoint_refines P k hk x hleft hright
  refines_right := Refines.refl _

/-- The scan-selected insertion packages the same common-refinement
certificate without requiring the caller to choose a cell index. -/
def insertLocatedPointCommonRefinement {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) :
    CommonRefinement P (insertLocatedPoint P x hleft hright) where
  refinement := insertLocatedPoint P x hleft hright
  refines_left := insertLocatedPoint_refines P x hleft hright
  refines_right := Refines.refl _

/-- A finite record of successive rational breakpoint insertions.  Each step
has its own cell-membership proof, so the resulting refinement is executable
finite data rather than an existential appeal to density of the rationals. -/
inductive InsertionChain {a b : Rat} :
    RationalPartition a b -> RationalPartition a b -> Type
  | refl (P : RationalPartition a b) : InsertionChain P P
  | insert {base current : RationalPartition a b}
      (chain : InsertionChain base current)
      (k : Nat) (hk : k < current.pieces) (x : Rat)
      (hleft : current.point k <= x) (hright : x <= current.point (k + 1)) :
      InsertionChain base (insertPoint current k hk x hleft hright)

/-- Extend an insertion chain by any rational point in the enclosing interval.
The finite scan chooses its containing cell, so a later list-merging algorithm
can add breakpoints without any external choice operation. -/
def InsertionChain.insertLocated {a b : Rat}
    {base current : RationalPartition a b}
    (chain : InsertionChain base current) (x : Rat)
    (hleft : a <= x) (hright : x <= b) :
    InsertionChain base (insertLocatedPoint current x hleft hright) :=
  let h := locateInsertionCell_spec current x hleft hright
  InsertionChain.insert chain (locateInsertionCell current x) h.1 x h.2.1 h.2.2

/-- Turn any finite list of rational points in `[a,b]` into an explicit
insertion chain.  The returned sigma pair contains both the final partition
and the proof-relevant sequence of finite scan-and-insert steps that produced
it. -/
def insertionChainOfPointList {a b : Rat} (P : RationalPartition a b) :
    (xs : List Rat) ->
    (forall x, x ∈ xs -> a <= x /\ x <= b) ->
    Sigma (InsertionChain P)
  | [], _ => ⟨P, InsertionChain.refl P⟩
  | x :: xs, hinside =>
      let htail : forall y, y ∈ xs -> a <= y /\ y <= b :=
        fun y hy => hinside y (List.mem_cons_of_mem x hy)
      let rest := insertionChainOfPointList P xs htail
      let hx := hinside x (by simp)
      ⟨insertLocatedPoint rest.1 x hx.1 hx.2,
        rest.2.insertLocated x hx.1 hx.2⟩

/-- A rational value occurs among a partition's finite breakpoint list. -/
def ContainsPoint {a b : Rat} (P : RationalPartition a b) (x : Rat) : Prop :=
  exists i, i <= P.pieces /\ P.point i = x

/-- A refinement preserves every explicitly occurring breakpoint. -/
theorem containsPoint_of_refines {a b : Rat}
    {fine coarse : RationalPartition a b} (R : Refines fine coarse)
    {x : Rat} (hx : coarse.ContainsPoint x) : fine.ContainsPoint x := by
  rcases hx with ⟨i, hi, hpoint⟩
  refine ⟨R.index i, R.index_le hi, ?_⟩
  rw [R.point_eq i hi, hpoint]

/-- The scan-selected insertion explicitly contains its inserted value. -/
theorem insertLocatedPoint_contains {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) :
    (insertLocatedPoint P x hleft hright).ContainsPoint x := by
  have h := locateInsertionCell_spec P x hleft hright
  refine ⟨locateInsertionCell P x + 1, ?_, ?_⟩
  · change locateInsertionCell P x + 1 <= P.pieces + 1
    omega
  · have hnot : ¬ (locateInsertionCell P x + 1 <= locateInsertionCell P x) := by
      omega
    simp [insertLocatedPoint, insertPoint, insertPointValue, hnot]

/-- Every member of an in-range finite list occurs in the breakpoint list
produced by the scan-and-insert construction. -/
theorem insertionChainOfPointList_contains {a b : Rat}
    (P : RationalPartition a b) :
    forall (xs : List Rat)
      (hinside : forall x, x ∈ xs -> a <= x /\ x <= b)
      {x : Rat}, x ∈ xs ->
        (insertionChainOfPointList P xs hinside).1.ContainsPoint x := by
  intro xs
  induction xs with
  | nil =>
      intro hinside x hx
      simp at hx
  | cons y ys ih =>
      intro hinside x hx
      let htail : forall z, z ∈ ys -> a <= z /\ z <= b :=
        fun z hz => hinside z (List.mem_cons_of_mem y hz)
      let rest := insertionChainOfPointList P ys htail
      have hy : a <= y /\ y <= b := hinside y (by simp)
      change (insertLocatedPoint rest.1 y hy.1 hy.2).ContainsPoint x
      rcases List.mem_cons.mp hx with hxy | hx
      · subst x
        exact insertLocatedPoint_contains rest.1 y hy.1 hy.2
      · exact containsPoint_of_refines
          (insertLocatedPoint_refines rest.1 y hy.1 hy.2)
          (ih htail hx)

/-- Scan a finite breakpoint list for the first occurrence of a rational
value.  The scan is total; its correctness theorem below is used only when
the value is known to occur. -/
def firstOccurrenceAux {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (i fuel : Nat) : Nat :=
  match fuel with
  | 0 => i
  | fuel + 1 =>
      if P.point i = x then i else firstOccurrenceAux P x (i + 1) fuel

/-- The leftmost-occurrence search over all actual breakpoint indices. -/
def firstOccurrence {a b : Rat} (P : RationalPartition a b) (x : Rat) : Nat :=
  firstOccurrenceAux P x 0 (P.pieces + 1)

/-- Correctness of the finite first-occurrence scan. -/
theorem firstOccurrenceAux_spec {a b : Rat} (P : RationalPartition a b)
    (x : Rat) :
    forall (i fuel j : Nat),
      i <= j -> j < i + fuel -> P.point j = x ->
      let k := firstOccurrenceAux P x i fuel
      i <= k /\ k <= j /\ P.point k = x := by
  intro i fuel
  induction fuel generalizing i with
  | zero =>
      intro j hij hj hpoint
      omega
  | succ fuel ih =>
      intro j hij hj hpoint
      simp only [firstOccurrenceAux]
      by_cases hi : P.point i = x
      · rw [if_pos hi]
        exact ⟨Nat.le_refl _, hij, hi⟩
      · rw [if_neg hi]
        have hijne : i ≠ j := by
          intro heq
          apply hi
          simpa [heq] using hpoint
        have hlt : i < j := Nat.lt_of_le_of_ne hij hijne
        rcases ih (i + 1) j (by omega) (by omega) hpoint with
          ⟨hfirst, hsecond, hvalue⟩
        exact ⟨Nat.le_trans (Nat.le_succ i) hfirst, hsecond, hvalue⟩

/-- If a rational value occurs in a partition, the finite scan finds its
leftmost occurrence and is no later than every other occurrence. -/
theorem firstOccurrence_spec {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hx : P.ContainsPoint x) :
    firstOccurrence P x <= P.pieces /\
      P.point (firstOccurrence P x) = x /\
      forall j, j <= P.pieces -> P.point j = x -> firstOccurrence P x <= j := by
  rcases hx with ⟨j, hj, hpoint⟩
  have hfound := firstOccurrenceAux_spec P x 0 (P.pieces + 1) j
    (Nat.zero_le _) (by omega) hpoint
  constructor
  · exact Nat.le_trans (by simpa [firstOccurrence] using hfound.2.1) hj
  constructor
  · simpa [firstOccurrence] using hfound.2.2
  · intro i hi hvalue
    have hfirst := firstOccurrenceAux_spec P x 0 (P.pieces + 1) i
      (Nat.zero_le _) (by omega) hvalue
    simpa [firstOccurrence] using hfirst.2.1

/-- The leftmost occurrence of the left endpoint is index zero. -/
theorem firstOccurrence_leftEndpoint {a b : Rat} (P : RationalPartition a b) :
    firstOccurrence P a = 0 := by
  have ha : P.ContainsPoint a := ⟨0, Nat.zero_le _, P.left_endpoint⟩
  apply Nat.eq_zero_of_le_zero
  exact (firstOccurrence_spec P a ha).2.2 0 (Nat.zero_le _) P.left_endpoint

/-- First occurrences preserve the rational order of values that occur in a
monotone partition. -/
theorem firstOccurrence_mono {a b : Rat} (P : RationalPartition a b)
    {x y : Rat} (hx : P.ContainsPoint x) (hy : P.ContainsPoint y)
    (hxy : x <= y) :
    firstOccurrence P x <= firstOccurrence P y := by
  by_cases hEq : x = y
  · subst y
    exact Nat.le_refl _
  · apply Nat.le_of_not_lt
    intro hindex
    have hspecX := firstOccurrence_spec P x hx
    have hspecY := firstOccurrence_spec P y hy
    have hyx : y <= x := by
      calc
        y = P.point (firstOccurrence P y) := hspecY.2.1.symm
        _ <= P.point (firstOccurrence P x) :=
          P.monotone _ _ (Nat.le_of_lt hindex) hspecX.1
        _ = x := hspecX.2.1
    exact hEq (Rat.le_antisymm hxy hyx)

/-- A refinement may be recovered constructively from the information that
every coarse breakpoint occurs somewhere in a fine monotone list. -/
def ContainsAllPoints {a b : Rat}
    (fine coarse : RationalPartition a b) : Prop :=
  forall i, i <= coarse.pieces -> fine.ContainsPoint (coarse.point i)

/-- The index used to recover an ordered refinement from point containment.
After the final coarse breakpoint it stays at the final fine breakpoint, so it
is a monotone total function on natural numbers as required by `Refines`. -/
def refinementIndex {a b : Rat}
    (fine coarse : RationalPartition a b) (i : Nat) : Nat :=
  let j := min i coarse.pieces
  if j = coarse.pieces then fine.pieces else firstOccurrence fine (coarse.point j)

theorem refinementIndex_le {a b : Rat}
    {fine coarse : RationalPartition a b}
    (hcontains : ContainsAllPoints fine coarse) (i : Nat) :
    refinementIndex fine coarse i <= fine.pieces := by
  simp only [refinementIndex]
  split
  · exact Nat.le_refl _
  · exact (firstOccurrence_spec fine _
      (hcontains _ (Nat.min_le_right _ _))).1

theorem refinementIndex_zero {a b : Rat}
    {fine coarse : RationalPartition a b} :
    refinementIndex fine coarse 0 = 0 := by
  have hpositive : coarse.pieces ≠ 0 := Nat.ne_of_gt coarse.positive
  have hmin : min 0 coarse.pieces = 0 := Nat.min_eq_left (Nat.zero_le _)
  have hlast : ¬ (0 = coarse.pieces) := fun h => hpositive h.symm
  rw [refinementIndex, hmin, if_neg hlast]
  simpa [coarse.left_endpoint] using firstOccurrence_leftEndpoint fine

theorem refinementIndex_last {a b : Rat}
    (fine coarse : RationalPartition a b) :
    refinementIndex fine coarse coarse.pieces = fine.pieces := by
  simp [refinementIndex]

theorem refinementIndex_point_eq {a b : Rat}
    {fine coarse : RationalPartition a b}
    (hcontains : ContainsAllPoints fine coarse)
    {i : Nat} (hi : i <= coarse.pieces) :
    fine.point (refinementIndex fine coarse i) = coarse.point i := by
  have hmin : min i coarse.pieces = i := Nat.min_eq_left hi
  rw [refinementIndex, hmin]
  by_cases hlast : i = coarse.pieces
  · rw [if_pos hlast]
    subst i
    rw [fine.right_endpoint, coarse.right_endpoint]
  · rw [if_neg hlast]
    exact (firstOccurrence_spec fine _ (hcontains i hi)).2.1

theorem refinementIndex_mono {a b : Rat}
    {fine coarse : RationalPartition a b}
    (hcontains : ContainsAllPoints fine coarse)
    (i j : Nat) (hij : i <= j) :
    refinementIndex fine coarse i <= refinementIndex fine coarse j := by
  let i' := min i coarse.pieces
  let j' := min j coarse.pieces
  have hi' : i' <= coarse.pieces := Nat.min_le_right _ _
  have hj' : j' <= coarse.pieces := Nat.min_le_right _ _
  have hij' : i' <= j' := by
    dsimp [i', j']
    omega
  by_cases hilast : i' = coarse.pieces
  · have hjlast : j' = coarse.pieces := by
      apply Nat.le_antisymm hj'
      simpa [hilast] using hij'
    simp [refinementIndex, i', j', hilast, hjlast]
  · by_cases hjlast : j' = coarse.pieces
    · simp only [refinementIndex]
      rw [show min i coarse.pieces = i' by rfl,
        show min j coarse.pieces = j' by rfl, if_neg hilast, if_pos hjlast]
      exact (firstOccurrence_spec fine _ (hcontains i' hi')).1
    · simp only [refinementIndex]
      rw [show min i coarse.pieces = i' by rfl,
        show min j coarse.pieces = j' by rfl, if_neg hilast, if_neg hjlast]
      exact firstOccurrence_mono fine (hcontains i' hi') (hcontains j' hj')
        (coarse.monotone i' j' hij' hj')

/-- Point containment is sufficient to build the full finite refinement
certificate, including a monotone embedding of all coarse breakpoint indices. -/
def refinesOfContainsAllPoints {a b : Rat}
    {fine coarse : RationalPartition a b}
    (hcontains : ContainsAllPoints fine coarse) : Refines fine coarse where
  index := refinementIndex fine coarse
  index_zero := refinementIndex_zero
  index_last := refinementIndex_last fine coarse
  index_mono := refinementIndex_mono hcontains
  point_eq := fun _ hi => refinementIndex_point_eq hcontains hi

/-- The explicitly finite list of every breakpoint in a partition. -/
def breakpointList {a b : Rat} (P : RationalPartition a b) : List Rat :=
  (List.range (P.pieces + 1)).map P.point

theorem point_mem_breakpointList {a b : Rat} (P : RationalPartition a b)
    {i : Nat} (hi : i <= P.pieces) : P.point i ∈ P.breakpointList := by
  apply List.mem_map.mpr
  exact ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩

theorem point_in_bounds {a b : Rat} (P : RationalPartition a b)
    {i : Nat} (hi : i <= P.pieces) :
    a <= P.point i /\ P.point i <= b := by
  constructor
  · calc
      a = P.point 0 := P.left_endpoint.symm
      _ <= P.point i := P.monotone 0 i (Nat.zero_le _) hi
  · calc
      P.point i <= P.point P.pieces := P.monotone i P.pieces hi (Nat.le_refl _)
      _ = b := P.right_endpoint

theorem breakpointList_in_bounds {a b : Rat} (P : RationalPartition a b) :
    forall x, x ∈ P.breakpointList -> a <= x /\ x <= b := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, hi, hpoint⟩
  rw [← hpoint]
  apply P.point_in_bounds
  have hindex := List.mem_range.mp hi
  omega

/-- Insert every breakpoint of the right partition into the left one by a
deterministic finite scan.  The following theorem turns the resulting point
containment into both refinement certificates. -/
def partitionPointInsertionChain {a b : Rat}
    (left right : RationalPartition a b) : Sigma (InsertionChain left) :=
  insertionChainOfPointList left right.breakpointList (breakpointList_in_bounds right)

theorem partitionPointInsertionChain_contains {a b : Rat}
    (left right : RationalPartition a b) {i : Nat} (hi : i <= right.pieces) :
    (partitionPointInsertionChain left right).1.ContainsPoint (right.point i) := by
  apply insertionChainOfPointList_contains left right.breakpointList
    (breakpointList_in_bounds right)
  exact right.point_mem_breakpointList hi

/-- A finite insertion chain carries its composite refinement certificate back
to its starting breakpoint list. -/
noncomputable def InsertionChain.refines {a b : Rat}
    {base target : RationalPartition a b} :
    InsertionChain base target -> Refines target base := by
  intro chain
  induction chain with
  | refl =>
      exact Refines.refl _
  | insert chain k hk x hleft hright ih =>
      exact (insertPoint_refines _ k hk x hleft hright).trans ih

/-- Every endpoint of a finite insertion chain is a common refinement of its
initial partition and its final explicitly inserted breakpoint list. -/
noncomputable def InsertionChain.commonRefinement {a b : Rat}
    {base target : RationalPartition a b}
    (chain : InsertionChain base target) : CommonRefinement base target where
  refinement := target
  refines_left := chain.refines
  refines_right := Refines.refl target

/-- A general finite common-refinement construction for arbitrary rational
partitions.  It uses only the supplied breakpoint lists, bounded scans, and
the monotonicity proof already carried by each partition. -/
noncomputable def commonRefinementOfPartitions {a b : Rat}
    (left right : RationalPartition a b) : CommonRefinement left right :=
  let chain := partitionPointInsertionChain left right
  { refinement := chain.1
    refines_left := chain.2.refines
    refines_right := refinesOfContainsAllPoints
      (fun _ hi => partitionPointInsertionChain_contains left right hi) }

def cell {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) : RationalSubinterval a b where
  lower := P.point k
  upper := P.point (k + 1)
  lower_mem := by
    have hkPieces : k <= P.pieces := Nat.le_of_lt hk
    have h := P.monotone 0 k (Nat.zero_le k) hkPieces
    simpa [P.left_endpoint] using h
  ordered := by
    exact P.monotone k (k + 1) (Nat.le_succ k) (Nat.succ_le_of_lt hk)
  upper_mem := by
    have h := P.monotone (k + 1) P.pieces (Nat.succ_le_of_lt hk) (Nat.le_refl P.pieces)
    simpa [P.right_endpoint] using h

/-- Every genuine cell of an explicit uniform partition has exactly its
rational mesh width. -/
theorem uniform_cell_width (a b : Rat) (pieces : Nat)
    (hpieces : 0 < pieces) (hab : a <= b)
    (k : Nat) (hk : k < pieces) :
    ((uniform a b pieces hpieces hab).cell k hk).width =
      mesh a b pieces := by
  change leftPoint a b pieces (k + 1) - leftPoint a b pieces k =
    mesh a b pieces
  exact leftPoint_step a b pieces k

/-! Finite telescoping for rational adjacent increments.  This is the order
identity used when a cell-range width is split into a center increment and a
uniform tail contribution. -/

theorem rat_adjacent_difference_fold (points : Nat -> Rat) (n : Nat) :
    (List.range n).foldl
      (fun acc k => acc + (points (k + 1) - points k)) 0 =
      points n - points 0 := by
  induction n with
  | zero => simp [Rat.sub_self]
  | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rw [ih]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Regard a partition's breakpoint list as a total rational path by holding
its final value constant beyond the last cell.  This permits the finite
corner-sum estimates to apply directly to partition data. -/
def clampedPath {a b : Rat} (P : RationalPartition a b) (i : Nat) : Rat :=
  P.point (min i P.pieces)

theorem clampedPath_eq_point {a b : Rat} (P : RationalPartition a b)
    {i : Nat} (hi : i <= P.pieces) :
    P.clampedPath i = P.point i := by
  simp [clampedPath, Nat.min_eq_left hi]

/-- A finite upper bound for the widths of all genuine cells of a rational
partition.  The nonnegativity field makes the bound meaningful beyond the
last cell of the clamped path, where its increments are zero. -/
def MaxStepAtMost {a b : Rat} (P : RationalPartition a b) (delta : Rat) : Prop :=
  0 <= delta /\
    forall k, k < P.pieces -> P.point (k + 1) - P.point k <= delta

/-- Successive values of a clamped partition path are nondecreasing. -/
theorem clampedPath_step_nonnegative {a b : Rat}
    (P : RationalPartition a b) (i : Nat) :
    0 <= P.clampedPath (i + 1) - P.clampedPath i := by
  by_cases hi : i < P.pieces
  · have hmin : min i P.pieces = i := Nat.min_eq_left (Nat.le_of_lt hi)
    have hminsucc : min (i + 1) P.pieces = i + 1 :=
      Nat.min_eq_left (Nat.succ_le_of_lt hi)
    have hmono := P.monotone i (i + 1) (Nat.le_succ i) (Nat.succ_le_of_lt hi)
    rw [clampedPath, clampedPath, hmin, hminsucc]
    grind [Rat.sub_eq_add_neg]
  · have hpieces : P.pieces <= i := Nat.le_of_not_gt hi
    have hmin : min i P.pieces = P.pieces := Nat.min_eq_right hpieces
    have hminsucc : min (i + 1) P.pieces = P.pieces :=
      Nat.min_eq_right (Nat.le_trans hpieces (Nat.le_succ i))
    rw [clampedPath, clampedPath, hmin, hminsucc]
    grind [Rat.sub_eq_add_neg]

/-- A cell-width bound transfers to every increment of the total clamped
path.  This supplies the first factor required by the finite corner-area
estimate, including the zero increments after the final partition cell. -/
theorem clampedPath_step_le_of_maxStep {a b : Rat}
    (P : RationalPartition a b) (delta : Rat)
    (hstep : P.MaxStepAtMost delta) (i : Nat) :
    P.clampedPath (i + 1) - P.clampedPath i <= delta := by
  by_cases hi : i < P.pieces
  · have hmin : min i P.pieces = i := Nat.min_eq_left (Nat.le_of_lt hi)
    have hminsucc : min (i + 1) P.pieces = i + 1 :=
      Nat.min_eq_left (Nat.succ_le_of_lt hi)
    rw [clampedPath, clampedPath, hmin, hminsucc]
    exact hstep.2 i hi
  · have hpieces : P.pieces <= i := Nat.le_of_not_gt hi
    have hmin : min i P.pieces = P.pieces := Nat.min_eq_right hpieces
    have hminsucc : min (i + 1) P.pieces = P.pieces :=
      Nat.min_eq_right (Nat.le_trans hpieces (Nat.le_succ i))
    rw [clampedPath, clampedPath, hmin, hminsucc]
    calc
      P.point P.pieces - P.point P.pieces = 0 := by
        grind [Rat.sub_eq_add_neg]
      _ <= delta := hstep.1

/-- Exact finite integration by parts on an arbitrary certified rational
partition.  The two functions are sampled at the supplied breakpoints (and
the total clamped path makes the samples harmless beyond the final cell).
This is the partition-level form used by later certified integral arguments:
it is still a rational finite-sum identity, not an FTC or a claim about an
unconstructed integral. -/
theorem finiteIntegrationByParts_onPartition {a b : Rat}
    (P : RationalPartition a b) (f g : Rat -> Rat) :
    leftStieltjesSum (fun i => f (P.clampedPath i))
        (fun i => g (P.clampedPath i)) P.pieces +
      rightStieltjesSum (fun i => f (P.clampedPath i))
        (fun i => g (P.clampedPath i)) P.pieces =
      f b * g b - f a * g a := by
  simpa [clampedPath, P.left_endpoint, P.right_endpoint] using
    (finiteIntegrationByParts
      (fun i => f (P.clampedPath i))
      (fun i => g (P.clampedPath i)) P.pieces)

/-- The corresponding arbitrary-partition identity when both Stieltjes sums
use left endpoints.  The sole discrepancy from the endpoint-product formula
is the explicit finite corner correction.  This is the version consumed by
monotone-piece error bounds in constructive integration by parts. -/
theorem finiteIntegrationByParts_withVariation_onPartition {a b : Rat}
    (P : RationalPartition a b) (f g : Rat -> Rat) :
    leftStieltjesSum (fun i => f (P.clampedPath i))
        (fun i => g (P.clampedPath i)) P.pieces +
      leftStieltjesSum (fun i => g (P.clampedPath i))
        (fun i => f (P.clampedPath i)) P.pieces +
      quadraticVariationSum (fun i => f (P.clampedPath i))
        (fun i => g (P.clampedPath i)) P.pieces =
      f b * g b - f a * g a := by
  simpa [clampedPath, P.left_endpoint, P.right_endpoint] using
    (finiteIntegrationByParts_withVariation
      (fun i => f (P.clampedPath i))
      (fun i => g (P.clampedPath i)) P.pieces)

/-- The constructive finite integration-by-parts estimate on an arbitrary
certified rational partition.  If the sampled second factor is nondecreasing,
the two left Stieltjes strips differ from the endpoint product by at most the
partition mesh times that factor's endpoint variation.

This is an exact finite certificate: it does not identify either strip with a
definite integral or invoke a limiting partition.  It is the form consumed by
the later monotone-piece FTC construction. -/
theorem coordinateIntegrationByParts_onPartition_endpoint_bracket {a b : Rat}
    (P : RationalPartition a b) (v : Rat -> Rat) (delta : Rat)
    (hstep : P.MaxStepAtMost delta)
    (hv : forall i,
      0 <= v (P.clampedPath (i + 1)) - v (P.clampedPath i)) :
    b * v b - a * v a - delta * (v b - v a) <=
      leftStieltjesSum P.clampedPath
          (fun i => v (P.clampedPath i)) P.pieces +
        leftStieltjesSum (fun i => v (P.clampedPath i))
          P.clampedPath P.pieces /\
      leftStieltjesSum P.clampedPath
          (fun i => v (P.clampedPath i)) P.pieces +
        leftStieltjesSum (fun i => v (P.clampedPath i))
          P.clampedPath P.pieces <=
        b * v b - a * v a := by
  let corner := quadraticVariationSum
    P.clampedPath
    (fun i => v (P.clampedPath i)) P.pieces
  have hidentity := finiteIntegrationByParts_withVariation_onPartition P
    (fun x => x) v
  have hcorner_nonneg : 0 <= corner := by
    dsimp [corner]
    exact quadraticVariationSum_nonneg_of_step_nonnegative
      P.clampedPath
      (fun i => v (P.clampedPath i))
      (clampedPath_step_nonnegative P) hv P.pieces
  have hcorner_le : corner <= delta * (v b - v a) := by
    dsimp [corner]
    simpa [clampedPath, P.left_endpoint, P.right_endpoint] using
      (quadraticVariationSum_le_stepBound_mul_endpointDifference
        P.clampedPath (fun i => v (P.clampedPath i)) delta
        (clampedPath_step_le_of_maxStep P delta hstep) hv P.pieces)
  dsimp [corner] at hcorner_nonneg hcorner_le
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- The explicit uniform partition has mesh as a certified bound for every
cell width. -/
theorem uniform_maxStepAtMost_mesh (a b : Rat) (pieces : Nat)
    (hpieces : 0 < pieces) (hab : a <= b) :
    (uniform a b pieces hpieces hab).MaxStepAtMost (mesh a b pieces) := by
  constructor
  · exact mesh_nonneg_of_le hpieces hab
  · intro k hk
    change leftPoint a b pieces (k + 1) - leftPoint a b pieces k <=
      mesh a b pieces
    rw [leftPoint_step]
    exact Rat.le_refl

/-- The finite corner correction between a partition coordinate path and any
nondecreasing rational path is controlled by the partition's explicit maximum
cell width times the endpoint variation of the latter path.  This is the
function-ready form of the geometric rectangle estimate: a later sampled
arctangent path need only supply its monotonicity. -/
theorem clampedPath_quadraticVariation_le_stepBound_mul_endpointDifference
    {a b : Rat} (P : RationalPartition a b) (v : Nat -> Rat) (delta : Rat)
    (hstep : P.MaxStepAtMost delta)
    (hv : forall i, 0 <= v (i + 1) - v i) :
    quadraticVariationSum P.clampedPath v P.pieces <=
      delta * (v P.pieces - v 0) :=
  quadraticVariationSum_le_stepBound_mul_endpointDifference
    P.clampedPath v delta (clampedPath_step_le_of_maxStep P delta hstep) hv P.pieces

/-- On a uniform rational partition the preceding estimate takes its expected
mesh form.  It is independent of how the nondecreasing second path was
obtained, so it applies equally to geometric, series, or inverse-function
sample values. -/
theorem uniform_clampedPath_quadraticVariation_le_mesh_mul_endpointDifference
    (a b : Rat) (pieces : Nat) (hpieces : 0 < pieces) (hab : a <= b)
    (v : Nat -> Rat) (hv : forall i, 0 <= v (i + 1) - v i) :
    quadraticVariationSum (uniform a b pieces hpieces hab).clampedPath v pieces <=
      mesh a b pieces * (v pieces - v 0) := by
  simpa [uniform] using
    clampedPath_quadraticVariation_le_stepBound_mul_endpointDifference
      (uniform a b pieces hpieces hab) v (mesh a b pieces)
      (uniform_maxStepAtMost_mesh a b pieces hpieces hab) hv

/-- The nonnegative corner correction for a partition's own monotone
breakpoint path is bounded by the square of its endpoint variation.  This
instantiates the geometric finite integration-by-parts estimate on an actual
rational partition, ready for cellwise mesh bounds. -/
theorem clampedPath_quadraticVariation_le_endpointSquare {a b : Rat}
    (P : RationalPartition a b) :
    quadraticVariationSum P.clampedPath P.clampedPath P.pieces <=
      (b - a) * (b - a) := by
  have h := quadraticVariationSum_le_endpointVariationProduct_of_step_nonnegative
    P.clampedPath P.clampedPath
    (clampedPath_step_nonnegative P) (clampedPath_step_nonnegative P) P.pieces
  simpa [clampedPath, P.left_endpoint, P.right_endpoint] using h

/-- The total interval contribution of one index to a derivative-bound sum.
The out-of-range branch is deliberately the degenerate zero interval, making
finite fold arguments total even before a list-membership fact is supplied. -/
def boundIntegralTerm {a b : Rat} (P : RationalPartition a b)
    (bound : (k : Nat) -> k < P.pieces -> QInterval) (k : Nat) : QInterval :=
  if hk : k < P.pieces then
    (P.cell k hk).scaleBound (bound k hk)
  else
    { lo := 0, hi := 0 }

/-- The matching total interval contribution of a cell endpoint difference at
one fixed function-evaluation stage. -/
def endpointDifferenceTerm {a b : Rat} (P : RationalPartition a b)
    (F : RealFunRaw) (prec k : Nat) : QInterval :=
  if _ : k < P.pieces then
    endpointDifferenceInterval F (P.point k) (P.point (k + 1)) prec
  else
    { lo := 0, hi := 0 }

/-- A generic finite addition fold preserves interval containment when every
summand does.  It is the exact finite-sum transport used by the FTC assembly
below. -/
theorem addInterval_fold_contains (xs : List Nat)
    (outer inner : Nat -> QInterval) {outerInit innerInit : QInterval}
    (hinit : outerInit.ContainsInterval innerInit)
    (hterm : forall k, (outer k).ContainsInterval (inner k)) :
    ((xs.foldl (fun acc k => QInterval.addInterval acc (outer k)) outerInit)
      ).ContainsInterval
      (xs.foldl (fun acc k => QInterval.addInterval acc (inner k)) innerInit) := by
  induction xs generalizing outerInit innerInit with
  | nil =>
      exact hinit
  | cons k xs ih =>
      exact ih
        (QInterval.addInterval_contains hinit (hterm k))

/-- Moving a rational initial value outside a finite addition fold. -/
theorem rat_add_fold_initial (xs : List Nat) (term : Nat -> Rat)
    (initial : Rat) :
    xs.foldl (fun total k => total + term k) initial =
      initial + xs.foldl (fun total k => total + term k) 0 := by
  induction xs generalizing initial with
  | nil =>
      grind
  | cons k xs ih =>
      simp only [List.foldl]
      rw [ih (initial + term k)]
      rw [show (0 : Rat) + term k = term k by grind, ih (term k)]
      grind [Rat.add_assoc]

/-- Pointwise inequalities add through rational finite addition folds. -/
theorem rat_add_fold_le_of_pointwise (xs : List Nat)
    (left right : Nat -> Rat)
    (hterm : forall k, k ∈ xs -> left k <= right k) :
    xs.foldl (fun total k => total + left k) 0 <=
      xs.foldl (fun total k => total + right k) 0 := by
  induction xs with
  | nil =>
      exact Rat.le_refl
  | cons k xs ih =>
      simp only [List.foldl, Rat.zero_add]
      rw [rat_add_fold_initial xs left (left k),
        rat_add_fold_initial xs right (right k)]
      exact rat_add_le_add
        (hterm k (by simp))
        (ih (fun j hj => hterm j (List.mem_cons_of_mem k hj)))

/-- A rational addition fold is the ordinary sum of the mapped finite list. -/
theorem rat_add_fold_eq_map_sum (xs : List Nat) (term : Nat -> Rat) :
    xs.foldl (fun total k => total + term k) 0 = (xs.map term).sum := by
  rw [List.sum_eq_foldl, List.foldl_map]

/-- A common rational factor can be moved outside a finite addition fold. -/
theorem rat_add_fold_mul_right (xs : List Nat) (term : Nat -> Rat) (r : Rat) :
    xs.foldl (fun total k => total + term k * r) 0 =
      xs.foldl (fun total k => total + term k) 0 * r := by
  induction xs with
  | nil => grind
  | cons k xs ih =>
      simp only [List.foldl, Rat.zero_add]
      rw [rat_add_fold_initial xs (fun j => term j * r) (term k * r),
        rat_add_fold_initial xs term (term k), ih]
      grind [Rat.add_mul]

/-- Reversing the enumeration of a finite natural range does not change a
rational addition fold.  The reflected index is kept explicit for finite
partition reindexing arguments. -/
theorem rat_add_fold_range_reflect (n : Nat) (term : Nat -> Rat) :
    (List.range n).foldl (fun total k => total + term k) 0 =
      (List.range n).foldl
        (fun total k => total + term (n - 1 - k)) 0 := by
  rw [rat_add_fold_eq_map_sum, rat_add_fold_eq_map_sum]
  have hrange : (List.range n).reverse =
      List.map (fun k => n - 1 - k) (List.range n) := by
    calc
      (List.range n).reverse = (List.range' 0 n).reverse := by
        rw [← List.range_eq_range']
      _ = List.map (fun k => n - 1 - k) (List.range n) := by
        simpa using (List.reverse_range' (s := 0) (n := n))
  have hmap :
      List.map (fun k => term (n - 1 - k)) (List.range n) =
        List.map term (List.map (fun k => n - 1 - k) (List.range n)) := by
    rw [List.map_map]
    rfl
  rw [hmap, ← hrange, List.map_reverse, List.sum_reverse]

/-- Pointwise absolute-error bounds add through two rational finite sums. -/
theorem qabs_rat_add_fold_sub_fold_le (xs : List Nat)
    (left right bound : Nat -> Rat)
    (hterm : forall k, k ∈ xs -> qabs (left k - right k) <= bound k) :
    qabs
        (xs.foldl (fun total k => total + left k) 0 -
          xs.foldl (fun total k => total + right k) 0) <=
      xs.foldl (fun total k => total + bound k) 0 := by
  induction xs with
  | nil =>
      simp only [List.foldl]
      rw [Rat.sub_self]
      rw [qabs_eq_self_of_nonneg (by decide +kernel)]
      exact Rat.le_refl
  | cons k xs ih =>
      simp only [List.foldl]
      rw [Rat.zero_add, Rat.zero_add, Rat.zero_add]
      rw [rat_add_fold_initial xs left (left k),
        rat_add_fold_initial xs right (right k),
        rat_add_fold_initial xs bound (bound k)]
      have hk := hterm k (by simp)
      have hrest := ih (fun j hj => hterm j (List.mem_cons_of_mem k hj))
      have hdecomp :
          (left k + xs.foldl (fun total j => total + left j) 0) -
              (right k + xs.foldl (fun total j => total + right j) 0) =
            (left k - right k) +
              (xs.foldl (fun total j => total + left j) 0 -
                xs.foldl (fun total j => total + right j) 0) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hdecomp]
      calc
        qabs ((left k - right k) +
            (xs.foldl (fun total j => total + left j) 0 -
              xs.foldl (fun total j => total + right j) 0)) <=
          qabs (left k - right k) +
            qabs (xs.foldl (fun total j => total + left j) 0 -
              xs.foldl (fun total j => total + right j) 0) :=
            qabs_add_le _ _
        _ <= bound k + xs.foldl (fun total j => total + bound j) 0 :=
          rat_add_le_add hk hrest

/-- Interval addition folds add enclosure widths exactly, including a
possibly nonzero initial interval. -/
theorem addInterval_fold_width (xs : List Nat) (term : Nat -> QInterval)
    (initial : QInterval) :
    (xs.foldl (fun acc k => QInterval.addInterval acc (term k)) initial).width =
      initial.width + xs.foldl (fun total k => total + (term k).width) 0 := by
  induction xs generalizing initial with
  | nil =>
      grind
  | cons k xs ih =>
      change
        (xs.foldl (fun acc j => QInterval.addInterval acc (term j))
          (QInterval.addInterval initial (term k))).width =
          initial.width + xs.foldl (fun total j => total + (term j).width)
            (0 + (term k).width)
      rw [ih (QInterval.addInterval initial (term k))]
      rw [QInterval.addInterval_width]
      rw [show (0 : Rat) + (term k).width = (term k).width by grind]
      rw [rat_add_fold_initial xs (fun j => (term j).width) (term k).width]
      grind [Rat.add_assoc]

/-- A finite rational addition fold whose every term is bounded above by a
constant is bounded by that constant times the number of terms. -/
theorem rat_add_fold_le_length_mul (xs : List Nat) (term : Nat -> Rat)
    (c : Rat) (hterm : forall k, k ∈ xs -> term k <= c) :
    xs.foldl (fun total k => total + term k) 0 <= (xs.length : Rat) * c := by
  induction xs with
  | nil =>
      simp
  | cons k xs ih =>
      have hrest : xs.foldl (fun total k => total + term k) 0 <=
          (xs.length : Rat) * c :=
        ih (fun j hj => hterm j (List.mem_cons_of_mem k hj))
      have hk : term k <= c := hterm k (by simp)
      simp only [List.length_cons]
      rw [Rat.natCast_add]
      have hone : ((1 : Nat) : Rat) = 1 := by decide +kernel
      rw [hone]
      calc
        (k :: xs).foldl (fun total j => total + term j) 0 =
            xs.foldl (fun total j => total + term j) (term k) := by
              simp only [List.foldl, Rat.zero_add]
        _ = term k + xs.foldl (fun total j => total + term j) 0 :=
          rat_add_fold_initial xs term (term k)
        _ <= c + (xs.length : Rat) * c := rat_add_le_add hk hrest
        _ = ((xs.length : Rat) + 1) * c := by
          grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm]

def boundIntegralSum {a b : Rat} (P : RationalPartition a b)
    (bound : (k : Nat) -> k < P.pieces -> QInterval) : QInterval :=
  (List.range P.pieces).foldl
    (fun acc k => QInterval.addInterval acc (P.boundIntegralTerm bound k))
    { lo := 0, hi := 0 }

theorem boundIntegralTerm_lo_eq_zero_of_bound_lo_zero
    {a b : Rat} (P : RationalPartition a b)
    (bound : (k : Nat) -> k < P.pieces -> QInterval)
    (hbound : forall k (hk : k < P.pieces), (bound k hk).lo = 0)
    (k : Nat) :
    (P.boundIntegralTerm bound k).lo = 0 := by
  by_cases hk : k < P.pieces
  · rw [boundIntegralTerm, dif_pos hk]
    unfold RationalSubinterval.scaleBound QInterval.scaleByRat
    have hwidth : 0 <= (P.cell k hk).width := by
      unfold RationalSubinterval.width
      have hordered := (P.cell k hk).ordered
      grind [Rat.sub_eq_add_neg]
    rw [if_pos hwidth, hbound k hk]
    exact Rat.mul_zero _
  · rw [boundIntegralTerm, dif_neg hk]

/-- If every supplied cell range starts at zero, the complete finite Darboux
sum starts at zero as well.  This is literal fold algebra and is useful for
nonnegative special-function quadratures. -/
theorem boundIntegralSum_lo_eq_zero_of_bound_lo_zero
    {a b : Rat} (P : RationalPartition a b)
    (bound : (k : Nat) -> k < P.pieces -> QInterval)
    (hbound : forall k (hk : k < P.pieces), (bound k hk).lo = 0) :
    (P.boundIntegralSum bound).lo = 0 := by
  have hfold : forall (xs : List Nat) (initial : QInterval),
      initial.lo = 0 ->
      (xs.foldl
        (fun acc k => QInterval.addInterval acc
          (P.boundIntegralTerm bound k)) initial).lo = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro initial hinitial
        exact hinitial
    | cons k xs ih =>
        intro initial hinitial
        simp only [List.foldl]
        apply ih
        unfold QInterval.addInterval
        rw [hinitial,
          P.boundIntegralTerm_lo_eq_zero_of_bound_lo_zero bound hbound k]
        exact Rat.zero_add 0
  unfold boundIntegralSum
  exact hfold (List.range P.pieces) { lo := 0, hi := 0 } rfl

/-- The finite sum of computed endpoint differences over the cells of a
rational partition, all evaluated at one common stage. -/
def endpointDifferenceSum {a b : Rat} (P : RationalPartition a b)
    (F : RealFunRaw) (prec : Nat) : QInterval :=
  (List.range P.pieces).foldl
    (fun acc k => QInterval.addInterval acc (P.endpointDifferenceTerm F prec k))
    { lo := 0, hi := 0 }

/-- If each derivative box on a uniform rational partition has width at most
`eps`, then the width of the finite scaled sum is at most the interval length
times `eps`.  This is a literal finite-fold calculation: the cell widths sum
to `b-a`, without invoking a limiting integral theorem. -/
theorem uniform_boundIntegralSum_width_le {a b : Rat}
    (pieces : Nat) (hpieces : 0 < pieces) (hab : a <= b)
    (bound : (k : Nat) -> k < pieces -> QInterval) (eps : Rat)
    (hbound : forall k (hk : k < pieces), (bound k hk).width <= eps) :
    ((uniform a b pieces hpieces hab).boundIntegralSum bound).width <=
      (b - a) * eps := by
  have hmesh : 0 <= mesh a b pieces := mesh_nonneg_of_le hpieces hab
  have hsum := rat_add_fold_le_length_mul (List.range pieces)
    (fun k => ((uniform a b pieces hpieces hab).boundIntegralTerm bound k).width)
    (mesh a b pieces * eps) (by
      intro k hk
      have hklt : k < pieces := List.mem_range.mp hk
      have hcell : 0 <= ((uniform a b pieces hpieces hab).cell k hklt).width := by
        rw [uniform_cell_width a b pieces hpieces hab k hklt]
        exact hmesh
      change
        (if hk : k < pieces then
          ((uniform a b pieces hpieces hab).cell k hk).scaleBound (bound k hk)
        else { lo := 0, hi := 0 }).width <= mesh a b pieces * eps
      rw [dif_pos hklt]
      unfold RationalSubinterval.scaleBound
      rw [QInterval.scaleByRat_width_of_nonneg hcell,
        uniform_cell_width a b pieces hpieces hab k hklt]
      exact Rat.mul_le_mul_of_nonneg_left (hbound k hklt) hmesh)
  calc
    ((uniform a b pieces hpieces hab).boundIntegralSum bound).width =
        (List.range pieces).foldl
          (fun total k => total +
            ((uniform a b pieces hpieces hab).boundIntegralTerm bound k).width) 0 := by
          unfold boundIntegralSum
          rw [addInterval_fold_width]
          change ({ lo := 0, hi := 0 } : QInterval).width + (List.range pieces).foldl
            (fun total k => total +
              ((uniform a b pieces hpieces hab).boundIntegralTerm bound k).width) 0 = _
          have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
            unfold QInterval.width
            grind
          rw [hzero]
          grind
    _ <= (pieces : Rat) * (mesh a b pieces * eps) := by
      simpa using hsum
    _ = (b - a) * eps := by
      have hpiecesRat : (pieces : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 hpieces)
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hpieces)]
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]

/-- The same finite width estimate with a bound indexed only by the cell
number.  Concrete algorithms normally compute one bound for each grid point;
the proof that the index is below the finite piece count should not become
part of that algorithm's type. -/
theorem uniform_boundIntegralSum_width_le_indexed {a b : Rat}
    (pieces : Nat) (hpieces : 0 < pieces) (hab : a <= b)
    (bound : Nat -> QInterval) (eps : Rat)
    (hbound : forall k, k < pieces -> (bound k).width <= eps) :
    ((uniform a b pieces hpieces hab).boundIntegralSum
      (fun k _ => bound k)).width <= (b - a) * eps := by
  apply uniform_boundIntegralSum_width_le pieces hpieces hab
    (fun k _ => bound k) eps
  intro k hk
  exact hbound k hk

/-- The recursive prefix form of `endpointDifferenceSum`.  It avoids any
hidden reindexing while proving the finite telescope. -/
def endpointDifferencePrefix {a b : Rat} (P : RationalPartition a b)
    (F : RealFunRaw) (prec : Nat) : Nat -> QInterval
  | 0 => { lo := 0, hi := 0 }
  | n + 1 => QInterval.addInterval (P.endpointDifferencePrefix F prec n)
      (endpointDifferenceInterval F (P.point n) (P.point (n + 1)) prec)

/-- The range-fold and recursive presentations of the endpoint-difference
sum agree for every genuine partition prefix. -/
theorem endpointDifferencePrefix_eq_rangeFold {a b : Rat}
    (P : RationalPartition a b) (F : RealFunRaw) (prec n : Nat)
    (hn : n <= P.pieces) :
    (List.range n).foldl
        (fun acc k => QInterval.addInterval acc (P.endpointDifferenceTerm F prec k))
        { lo := 0, hi := 0 } =
      P.endpointDifferencePrefix F prec n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < P.pieces := Nat.lt_of_succ_le hn
      rw [List.range_succ, List.foldl_append, ih (Nat.le_of_succ_le hn)]
      simp only [List.foldl_cons, List.foldl_nil, endpointDifferenceTerm,
        dif_pos hnlt]
      rfl

/-- A positive endpoint-difference prefix encloses the direct endpoint
difference from its first to its last breakpoint.  Interior evaluation-box
widths are accounted for constructively by the adjacent-cell enclosure
lemma; no cancellation of approximations is assumed. -/
theorem endpointDifferencePrefix_contains {a b : Rat}
    (P : RationalPartition a b) (F : RealFunRaw) (prec : Nat)
    (hF : F.Valid)
    (hdomain : forall i, i <= P.pieces -> F.domain (P.point i)) :
    forall n, 0 < n -> n <= P.pieces ->
      (P.endpointDifferencePrefix F prec n).ContainsInterval
        (endpointDifferenceInterval F (P.point 0) (P.point n) prec) := by
  intro n hnpos hnle
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero _ hnpos)
  | succ n ih =>
      by_cases hnzero : n = 0
      · subst n
        simpa [endpointDifferencePrefix, QInterval.zero_addInterval] using
          (QInterval.containsInterval_refl
            (endpointDifferenceInterval F (P.point 0) (P.point 1) prec))
      · have hprefix := ih (Nat.zero_lt_of_ne_zero hnzero)
          (Nat.le_of_succ_le hnle)
        have hmiddle := (hF (P.point n)
          (hdomain n (Nat.le_of_succ_le hnle))).1 prec
        have hadd := QInterval.addInterval_contains hprefix
          (QInterval.containsInterval_refl
            (endpointDifferenceInterval F (P.point n) (P.point (n + 1)) prec))
        have hadj := endpointDifferenceInterval_adjacent_additive_contains
          (F := F) (a := P.point 0) (b := P.point n) (c := P.point (n + 1))
          (prec := prec) hmiddle
        simpa [endpointDifferencePrefix] using hadd.trans hadj

/-- The finite sum of all adjacent endpoint-difference boxes encloses the
single endpoint-difference box across the whole partition. -/
theorem endpointDifferenceSum_contains {a b : Rat}
    (P : RationalPartition a b) (F : RealFunRaw) (prec : Nat)
    (hF : F.Valid)
    (hdomain : forall i, i <= P.pieces -> F.domain (P.point i)) :
    (P.endpointDifferenceSum F prec).ContainsInterval
      (endpointDifferenceInterval F a b prec) := by
  rw [endpointDifferenceSum,
    endpointDifferencePrefix_eq_rangeFold P F prec P.pieces (Nat.le_refl _)]
  have hprefix := endpointDifferencePrefix_contains P F prec hF hdomain
    P.pieces P.positive (Nat.le_refl _)
  simpa [P.left_endpoint, P.right_endpoint] using hprefix

/-- Cellwise endpoint enclosures assemble into a global endpoint enclosure.
This is the finite telescoping core of the derivative-bound FTC: every local
scaled derivative box may be summed at one common evaluation stage, and the
result provably contains `F(b)-F(a)`. -/
theorem boundIntegralSum_contains_endpointDifference {a b : Rat}
    (P : RationalPartition a b) (F : RealFunRaw) (prec : Nat)
    (hF : F.Valid)
    (hdomain : forall i, i <= P.pieces -> F.domain (P.point i))
    (bound : (k : Nat) -> k < P.pieces -> QInterval)
    (hlocal : forall k (hk : k < P.pieces),
      ((P.cell k hk).scaleBound (bound k hk)).ContainsInterval
        (endpointDifferenceInterval F (P.point k) (P.point (k + 1)) prec)) :
    (P.boundIntegralSum bound).ContainsInterval
      (endpointDifferenceInterval F a b prec) := by
  have hsum : (P.boundIntegralSum bound).ContainsInterval
      (P.endpointDifferenceSum F prec) := by
    unfold boundIntegralSum endpointDifferenceSum
    apply addInterval_fold_contains (List.range P.pieces)
      (P.boundIntegralTerm bound) (P.endpointDifferenceTerm F prec)
      (QInterval.containsInterval_refl _)
    intro k
    unfold boundIntegralTerm endpointDifferenceTerm
    split
    · exact hlocal k _
    · exact QInterval.containsInterval_refl _
  exact hsum.trans (endpointDifferenceSum_contains P F prec hF hdomain)

/-- The global finite derivative-bound sum automatically overlaps the endpoint
difference it encloses.  Thus a common-stage local FTC proof need not list
overlap as an independent numerical axiom. -/
theorem boundIntegralSum_overlaps_endpointDifference {a b : Rat}
    (P : RationalPartition a b) (F : RealFunRaw) (prec : Nat)
    (hF : F.Valid)
    (hdomain : forall i, i <= P.pieces -> F.domain (P.point i))
    (bound : (k : Nat) -> k < P.pieces -> QInterval)
    (hlocal : forall k (hk : k < P.pieces),
      ((P.cell k hk).scaleBound (bound k hk)).ContainsInterval
        (endpointDifferenceInterval F (P.point k) (P.point (k + 1)) prec)) :
    QInterval.Overlaps (P.boundIntegralSum bound)
      (endpointDifferenceInterval F a b prec) := by
  apply QInterval.overlaps_of_contains_right
    (boundIntegralSum_contains_endpointDifference P F prec hF hdomain bound hlocal)
  simpa [P.left_endpoint, P.right_endpoint] using
    (endpointDifferenceInterval_width_nonneg hF
    (hdomain 0 (Nat.zero_le _))
    (hdomain P.pieces (Nat.le_refl _)) prec)

end RationalPartition

/-- A certified enclosure of derivative values on one rational subinterval.

This is the FTC-facing primitive: for every rational point in a short cell,
the pointwise derivative enclosure at the chosen evaluation precision is
contained in the supplied rational interval.  No convexity or differentiability
topology is mentioned here. -/
structure DerivativeBoundOnSubinterval
    (dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  bound : Nat -> QInterval
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> dF.domain x
  bound_ordered : forall n, 0 <= (bound n).width
  contains_values :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (bound n)
        (dF.compute x (evalPrecision n))

/-- Local endpoint control supplied by a derivative bound.  This is the
constructive substitute for invoking a classical mean-value theorem: the
scaled derivative range encloses the endpoint difference of the primitive on
this short cell. -/
structure LocalFTCFromDerivativeBound
    (F dF : RealFunRaw) {a b : Rat}
    (C : RationalSubinterval a b)
    (B : DerivativeBoundOnSubinterval dF C) where
  primitive_domain_lower : F.domain C.lower
  primitive_domain_upper : F.domain C.upper
  endpointPrecision : Nat -> Nat
  endpoint_contained :
    forall n,
      QInterval.ContainsInterval
        (C.scaleBound (B.bound n))
        (endpointDifferenceInterval F C.lower C.upper (endpointPrecision n))

/-- Local finite certificate that a candidate derivative matches the computed
secant behavior of the original function on one rational cell.

The `bound` field is the common rational interval enclosure.  The
`candidate_contained` field says the candidate derivative `dF` lies in that
bound at every rational point of the cell.  The
`endpoint_difference_contained` field says the actual endpoint difference of
`F` on the same cell is contained in the cell width times that bound.  Thus the
candidate derivative is not guessed: it is certified against finite secant
inequalities for the concrete algorithm. -/
structure CandidateDerivativeCellControl
    (F dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  bound : Nat -> QInterval
  derivativeEvalPrecision : Nat -> Nat
  endpointPrecision : Nat -> Nat
  primitive_domain_lower : F.domain C.lower
  primitive_domain_upper : F.domain C.upper
  candidate_domain_on : forall x, C.contains x -> dF.domain x
  bound_ordered : forall n, 0 <= (bound n).width
  candidate_contained :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (bound n)
        (dF.compute x (derivativeEvalPrecision n))
  endpoint_difference_contained :
    forall n,
      QInterval.ContainsInterval
        (C.scaleBound (bound n))
        (endpointDifferenceInterval F C.lower C.upper (endpointPrecision n))

namespace CandidateDerivativeCellControl

def toDerivativeBound
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C) :
    DerivativeBoundOnSubinterval dF C where
  bound := H.bound
  evalPrecision := H.derivativeEvalPrecision
  domain_on := H.candidate_domain_on
  bound_ordered := H.bound_ordered
  contains_values := H.candidate_contained

def toLocalFTC
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C) :
    LocalFTCFromDerivativeBound F dF C H.toDerivativeBound where
  primitive_domain_lower := H.primitive_domain_lower
  primitive_domain_upper := H.primitive_domain_upper
  endpointPrecision := H.endpointPrecision
  endpoint_contained := H.endpoint_difference_contained

/-- The finite mean-value bracket supplied by a cell certificate.

The scaled derivative range contains the actual endpoint increment, hence the
two rational boxes overlap.  This is the computable replacement for the
classical assertion that an attained intermediate derivative value realizes
the secant slope: no point-selection or completeness principle is needed. -/
theorem endpoint_difference_overlaps_bound
    {F dF : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C)
    (hF : F.Valid) (n : Nat) :
    QInterval.Overlaps
      (C.scaleBound (H.bound n))
      (endpointDifferenceInterval F C.lower C.upper (H.endpointPrecision n)) := by
  apply QInterval.overlaps_of_contains_right
    (H.endpoint_difference_contained n)
  exact endpointDifferenceInterval_width_nonneg hF
    H.primitive_domain_lower H.primitive_domain_upper _

end CandidateDerivativeCellControl

/-- FTC data based on derivative bounds over short rational cells.

The FTC-facing assumption is the derivative-range bound on each cell.  How
those bounds are produced is deliberately separate: monotonicity, convexity,
concavity, power-series tails, or formula-specific interval arithmetic can all
feed the same structure.

For each requested rational precision `eps`, the certificate chooses a rational
partition of `[a,b]`, derivative enclosures on its cells, and an endpoint
evaluation precision for `F(b)-F(a)`.  The summed derivative-bound interval is
the Riemann-style enclosure; the theorem-facing obligations are exactly that
this enclosure has width at most `eps`, the endpoint-difference interval has
width at most `eps`, and the two intervals overlap. -/
structure DerivativeBoundFTC (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  derivativeBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundOnSubinterval dF ((choosePartition eps).cell k hk)
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          (derivativeBound eps k hk)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk => (derivativeBound eps k hk).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk => (derivativeBound eps k hk).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace DerivativeBoundFTC

def boundedIntegralInterval
    {F dF : RealFunRaw} {a b : Rat}
  (h : DerivativeBoundFTC F dF a b) (eps : QPos) : QInterval :=
  (h.choosePartition eps).boundIntegralSum
    (fun k hk => (h.derivativeBound eps k hk).bound (h.chooseBoundStage eps))

def endpointInterval
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) (eps : QPos) : QInterval :=
  endpointDifferenceInterval F a b (h.chooseEndpointPrecision eps)

theorem closeAt
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) (eps : QPos) :
    QInterval.CloseAt (h.boundedIntegralInterval eps) (h.endpointInterval eps) eps := by
  exact ⟨h.overlap eps, h.riemann_width eps, h.endpoint_width eps⟩

def boundedIntegralCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : Nat -> QInterval :=
  fun n => h.boundedIntegralInterval (precisionAtStage n)

def endpointCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : Nat -> QInterval :=
  fun n => h.endpointInterval (precisionAtStage n)

def boundedIntegralRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : RealCompute where
  compute := h.boundedIntegralCompute

def endpointRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : RealCompute where
  compute := h.endpointCompute

/-- The derivative-bound FTC bridge, in computable-real form. -/
theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hgood := h.closeAt (precisionAtStage n)
  exact (RealCompute.compareAt_overlap_iff
    h.boundedIntegralRaw h.endpointRaw n n).2 hgood.1

end DerivativeBoundFTC

/-! A scheduled endpoint computation represents the same raw endpoint as the
canonical endpoint-difference computation.  The proof only uses nesting of
the two endpoint evaluators; no monotonicity of the schedule is required. -/
theorem DerivativeBoundFTC.endpointRaw_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b)
    (hF : F.Valid)
    (ha : F.domain a) (hb : F.domain b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    h.endpointRaw.Equiv (endpointDifferenceRaw F a b hendpoint) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  let s := h.chooseEndpointPrecision (precisionAtStage n)
  apply (RealCompute.compareAt_overlap_iff h.endpointRaw
    (endpointDifferenceRaw F a b hendpoint) n n).2
  change QInterval.Overlaps
    (endpointDifferenceInterval F a b s)
    (endpointDifferenceInterval F a b n)
  unfold endpointDifferenceInterval QInterval.Overlaps
  have hA := hF a ha
  have hB := hF b hb
  by_cases hsn : s <= n
  · have hAs := hA.2.1 s n hsn
    have hBs := hB.2.1 s n hsn
    change (F.compute a s).lo <= (F.compute a n).lo /\
      (F.compute a n).lo <= (F.compute a n).hi /\
      (F.compute a n).hi <= (F.compute a s).hi at hAs
    change (F.compute b s).lo <= (F.compute b n).lo /\
      (F.compute b n).lo <= (F.compute b n).hi /\
      (F.compute b n).hi <= (F.compute b s).hi at hBs
    grind
  · have hns : n <= s := by omega
    have hAn := hA.2.1 n s hns
    have hBn := hB.2.1 n s hns
    change (F.compute a n).lo <= (F.compute a s).lo /\
      (F.compute a s).lo <= (F.compute a s).hi /\
      (F.compute a s).hi <= (F.compute a n).hi at hAn
    change (F.compute b n).lo <= (F.compute b s).lo /\
      (F.compute b s).lo <= (F.compute b s).hi /\
      (F.compute b s).hi <= (F.compute b n).hi at hBn
    grind

/-- Top-level derivative-bound FTC bridge.

This is the public theorem name for the finite cell-bound route: once the
derivative-bound certificate supplies overlapping bounded-sum and endpoint
intervals at every selected computation stage, the two raw real algorithms are
equivalent. -/
theorem derivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw :=
  h.equiv_endpoint

/-! A streamlined effective-FTC certificate.  In `DerivativeBoundFTC` the
final overlap is exposed as a field for compatibility with older callers.
Here it is derived from the local endpoint containments: summing the scaled
derivative boxes contains the sum of the adjacent endpoint differences, and
the latter contains the global endpoint difference.  Thus this is the
interface intended for ordinary use: the analytic work is reduced to finite
derivative bounds and an arbitrarily small width schedule. -/

structure EffectiveDerivativeBoundFTC
    (F dF : RealFunRaw) (a b : Rat) where
  primitive_valid : F.Valid
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  derivativeBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundOnSubinterval dF
          ((choosePartition eps).cell k hk)
  domain_at_partition :
    forall eps i, i <= (choosePartition eps).pieces ->
      F.domain ((choosePartition eps).point i)
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          (derivativeBound eps k hk)
  endpointPrecision_agreement :
    forall eps k (hk : k < (choosePartition eps).pieces) n,
      (localControl eps k hk).endpointPrecision n =
        chooseEndpointPrecision eps
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          (derivativeBound eps k hk).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b
        (chooseEndpointPrecision eps)).width <= eps.val

def EffectiveDerivativeBoundFTC.toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b) :
    DerivativeBoundFTC F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  derivativeBound := h.derivativeBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := by
    intro eps
    apply RationalPartition.boundIntegralSum_overlaps_endpointDifference
      (h.choosePartition eps) F (h.chooseEndpointPrecision eps)
      h.primitive_valid (h.domain_at_partition eps)
    intro k hk
    have hlocal := (h.localControl eps k hk).endpoint_contained
      (h.chooseBoundStage eps)
    rw [h.endpointPrecision_agreement eps k hk (h.chooseBoundStage eps)] at hlocal
    simpa [RationalPartition.cell, RationalSubinterval.scaleBound] using hlocal

theorem effectiveDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

/-- The scheduled endpoint evaluator supplied by an effective FTC certificate
agrees with the canonical endpoint-difference evaluator of its primitive.
This is the representation-transport half of the public FTC interface: the
finite derivative certificate proves the scheduled evaluator correct, while
the primitive's own nested interval semantics transport it to the canonical
endpoint computation. -/
theorem EffectiveDerivativeBoundFTC.endpointRaw_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    h.toDerivativeBoundFTC.endpointRaw.Equiv
      (endpointDifferenceRaw F a b hendpoint) := by
  exact DerivativeBoundFTC.endpointRaw_equiv_endpointDifference
    h.toDerivativeBoundFTC h.primitive_valid
      h.primitive_domain_lower h.primitive_domain_upper hendpoint

/-- The complete effective FTC transport: the bounded finite Riemann raw is
equivalent to the canonical endpoint-difference raw.  The proof is finite at
each public stage.  The selected endpoint stage is used only to obtain a
telescope inside the bounded sum, then primitive interval nesting transports
that telescope to the requested canonical stage. -/
theorem EffectiveDerivativeBoundFTC.boundedIntegralRaw_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (endpointDifferenceRaw F a b hendpoint) := by
  let H := h.toDerivativeBoundFTC
  have hcanonical := h.endpointRaw_equiv_endpointDifference hendpoint
  intro n
  let eps := precisionAtStage n
  let s := H.chooseEndpointPrecision eps
  have hcontains :
      QInterval.ContainsInterval
        ((H.choosePartition eps).boundIntegralSum
          (fun k hk => (H.derivativeBound eps k hk).bound
            (H.chooseBoundStage eps)))
        (endpointDifferenceInterval F a b s) := by
    apply RationalPartition.boundIntegralSum_contains_endpointDifference
      (P := H.choosePartition eps) (F := F) (prec := s) h.primitive_valid
    · intro i hi
      exact h.domain_at_partition eps i hi
    · intro k hk
      have hlocal := (H.localControl eps k hk).endpoint_contained
        (H.chooseBoundStage eps)
      have hagree := h.endpointPrecision_agreement
        eps k hk (H.chooseBoundStage eps)
      have hagree' :
          (H.localControl eps k hk).endpointPrecision
              (H.chooseBoundStage eps) = s := by
        simpa [H, s, EffectiveDerivativeBoundFTC.toDerivativeBoundFTC] using hagree
      rw [hagree'] at hlocal
      simpa [RationalPartition.cell, s] using hlocal
  have hover2 := (RealCompute.compareAt_overlap_iff H.endpointRaw
      (endpointDifferenceRaw F a b hendpoint) n n).1
      (hcanonical n)
  apply (RealCompute.compareAt_overlap_iff H.boundedIntegralRaw
    (endpointDifferenceRaw F a b hendpoint) n n).2
  change QInterval.Overlaps
    ((H.choosePartition eps).boundIntegralSum
      (fun k hk => (H.derivativeBound eps k hk).bound (H.chooseBoundStage eps)))
    (endpointDifferenceCompute F a b n)
  change QInterval.Overlaps
    ((H.choosePartition eps).boundIntegralSum
      (fun k hk => (H.derivativeBound eps k hk).bound (H.chooseBoundStage eps)))
    (endpointDifferenceInterval F a b n)
  exact ⟨Rat.le_trans hcontains.1 hover2.1,
    Rat.le_trans hover2.2 hcontains.2⟩

/-- Global finite certificate for the "candidate derivative versus computed
secants" strategy.

For each requested precision, choose a rational partition.  On each cell,
`cellControl` supplies one rational interval family that simultaneously:

* contains the candidate derivative values, and
* contains the actual endpoint secant behavior of `F` after scaling by the
  cell width.

The remaining fields are exactly the numerical FTC closure conditions: the
summed bound interval and the endpoint-difference interval are narrow and
overlap. -/
structure CandidateDerivativeFTC (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  cellControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        CandidateDerivativeCellControl F dF ((choosePartition eps).cell k hk)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk => (cellControl eps k hk).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk => (cellControl eps k hk).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace CandidateDerivativeFTC

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    DerivativeBoundFTC F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  derivativeBound := fun eps k hk =>
    (h.cellControl eps k hk).toDerivativeBound
  localControl := fun eps k hk =>
    (h.cellControl eps k hk).toLocalFTC
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

/-- The closure theorem for the candidate-derivative strategy. -/
theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end CandidateDerivativeFTC

/-- Top-level closure theorem for the candidate-derivative strategy. -/
theorem candidateDerivativeFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-! A candidate FTC becomes a public endpoint theorem only after its
scheduled endpoint box has been connected to the canonical endpoint box at
the same public stage.  This is deliberately a separate certificate: the
finite derivative argument and the representation-specific endpoint
transport are different proof obligations. -/

structure CanonicalCandidateDerivativeFTC
    (F dF : RealFunRaw) (a b : Rat) where
  candidate : CandidateDerivativeFTC F dF a b
  integral_valid :
    candidate.toDerivativeBoundFTC.boundedIntegralRaw.Valid
  endpoint_valid :
    RealCompute.ValidCompute (endpointDifferenceCompute F a b)
  canonical_overlap :
    forall n,
      QInterval.Overlaps
        ((candidate.toDerivativeBoundFTC.boundedIntegralInterval
          (precisionAtStage n)))
        (endpointDifferenceInterval F a b n)

theorem CandidateDerivativeFTC.canonical_overlap_of_endpoint_stage_ge
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b)
    (hF : F.Valid) (ha : F.domain a) (hb : F.domain b)
    (hstage :
      forall n, n <= h.chooseEndpointPrecision (precisionAtStage n))
    (n : Nat) :
    QInterval.Overlaps
      (h.toDerivativeBoundFTC.boundedIntegralInterval (precisionAtStage n))
      (endpointDifferenceInterval F a b n) := by
  let s := h.chooseEndpointPrecision (precisionAtStage n)
  have hgood := h.overlap (precisionAtStage n)
  have hA := hF a ha
  have hB := hF b hb
  have hAs := hA.2.1 n s (hstage n)
  have hBs := hB.2.1 n s (hstage n)
  change (F.compute a n).lo <= (F.compute a s).lo /\
      (F.compute a s).lo <= (F.compute a s).hi /\
      (F.compute a s).hi <= (F.compute a n).hi at hAs
  change (F.compute b n).lo <= (F.compute b s).lo /\
      (F.compute b s).lo <= (F.compute b s).hi /\
      (F.compute b s).hi <= (F.compute b n).hi at hBs
  change QInterval.Overlaps
    (h.toDerivativeBoundFTC.boundedIntegralInterval (precisionAtStage n))
    (endpointDifferenceInterval F a b s) at hgood
  unfold QInterval.Overlaps endpointDifferenceInterval at hgood ⊢
  constructor
  · exact Rat.le_trans hgood.1 (by grind)
  · exact Rat.le_trans (by grind) hgood.2

namespace CanonicalCandidateDerivativeFTC

def integralRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : CanonicalCandidateDerivativeFTC F dF a b) : RealCompute :=
  h.candidate.toDerivativeBoundFTC.boundedIntegralRaw

def endpointRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : CanonicalCandidateDerivativeFTC F dF a b) : RealCompute :=
  endpointDifferenceRaw F a b h.endpoint_valid

theorem integral_equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : CanonicalCandidateDerivativeFTC F dF a b) :
    h.integralRaw.Equiv h.endpointRaw := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff h.integralRaw h.endpointRaw n n).2
  change QInterval.Overlaps
    (h.candidate.toDerivativeBoundFTC.boundedIntegralInterval
      (precisionAtStage n))
    (endpointDifferenceInterval F a b n)
  exact h.canonical_overlap n

theorem integral_equiv_canonical_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : CanonicalCandidateDerivativeFTC F dF a b) :
    h.integralRaw.Equiv
      (endpointDifferenceRaw F a b h.endpoint_valid) :=
  h.integral_equiv_endpoint

end CanonicalCandidateDerivativeFTC

/-- A stage-indexed variant of the finite candidate-derivative FTC.

Unlike `CandidateDerivativeFTC`, this certificate asks for local derivative
and secant information only at the *one common computation stage selected for
the requested outer precision*.  That is exactly the data supplied by an
epsilon--delta construction with a finite partition: all cells use one
uniform evaluation stage, their local endpoint boxes telescope, and their
summed width is controlled separately.  This avoids imposing an artificial
``all stages on a fixed cell'' obligation on a partition whose mesh is itself
chosen from the requested precision. -/
structure SelectedStageCandidateDerivativeFTC
    (F dF : RealFunRaw) (a b : Rat) where
  primitive_valid : F.Valid
  choosePartition : QPos -> RationalPartition a b
  chooseStage : QPos -> Nat
  derivativeBound :
    forall eps,
      forall k (_ : k < (choosePartition eps).pieces), QInterval
  primitive_domain_on :
    forall eps i, i <= (choosePartition eps).pieces ->
      F.domain ((choosePartition eps).point i)
  candidate_domain_on :
    forall eps k (hk : k < (choosePartition eps).pieces) x,
      ((choosePartition eps).cell k hk).contains x -> dF.domain x
  candidate_contained :
    forall eps k (hk : k < (choosePartition eps).pieces) x
      (_ : ((choosePartition eps).cell k hk).contains x),
      QInterval.ContainsInterval
        (derivativeBound eps k hk)
        (dF.compute x (chooseStage eps))
  local_endpoint_contained :
    forall eps k (hk : k < (choosePartition eps).pieces),
      QInterval.ContainsInterval
        (((choosePartition eps).cell k hk).scaleBound (derivativeBound eps k hk))
        (endpointDifferenceInterval F
          ((choosePartition eps).cell k hk).lower
          ((choosePartition eps).cell k hk).upper
          (chooseStage eps))
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk => derivativeBound eps k hk)).width <= eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseStage eps)).width <= eps.val

namespace SelectedStageCandidateDerivativeFTC

def boundedIntegralInterval
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) (eps : QPos) : QInterval :=
  (h.choosePartition eps).boundIntegralSum
    (fun k hk => h.derivativeBound eps k hk)

def endpointInterval
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) (eps : QPos) : QInterval :=
  endpointDifferenceInterval F a b (h.chooseStage eps)

/-- The finite telescope derives overlap from the local common-stage
enclosures, so it is not a further axiom of the certificate. -/
theorem overlap
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) (eps : QPos) :
    QInterval.Overlaps (h.boundedIntegralInterval eps) (h.endpointInterval eps) := by
  apply RationalPartition.boundIntegralSum_overlaps_endpointDifference
    (P := h.choosePartition eps) (F := F) (prec := h.chooseStage eps)
    h.primitive_valid
  · intro i hi
    exact h.primitive_domain_on eps i hi
  · intro k hk
    simpa [RationalPartition.cell] using h.local_endpoint_contained eps k hk

theorem closeAt
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) (eps : QPos) :
    QInterval.CloseAt (h.boundedIntegralInterval eps) (h.endpointInterval eps) eps := by
  exact ⟨h.overlap eps, h.riemann_width eps, h.endpoint_width eps⟩

def boundedIntegralCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) : Nat -> QInterval :=
  fun n => h.boundedIntegralInterval (precisionAtStage n)

def endpointCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) : Nat -> QInterval :=
  fun n => h.endpointInterval (precisionAtStage n)

def boundedIntegralRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) : RealCompute where
  compute := h.boundedIntegralCompute

def endpointRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) : RealCompute where
  compute := h.endpointCompute

/-- The selected-stage finite derivative sum and endpoint difference compute
the same raw real number. -/
theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hgood := h.closeAt (precisionAtStage n)
  exact (RealCompute.compareAt_overlap_iff
    h.boundedIntegralRaw h.endpointRaw n n).2 hgood.1

end SelectedStageCandidateDerivativeFTC

/-! A proof-irrelevance-friendly presentation of the selected-stage
certificate.  The interval bound depends on the cell number, but not on the
proof that the number is below the finite partition size.  This is equivalent
to `SelectedStageCandidateDerivativeFTC`; the indexed form is easier to
instantiate when a concrete partition is built from explicit breakpoints. -/

structure SelectedStageCandidateDerivativeFTCIndexed
    (F dF : RealFunRaw) (a b : Rat) where
  primitive_valid : F.Valid
  choosePartition : QPos -> RationalPartition a b
  chooseStage : QPos -> Nat
  derivativeBound : QPos -> Nat -> QInterval
  primitive_domain_on :
    forall eps i, i <= (choosePartition eps).pieces ->
      F.domain ((choosePartition eps).point i)
  candidate_domain_on :
    forall eps k (hk : k < (choosePartition eps).pieces) x,
      ((choosePartition eps).cell k hk).contains x -> dF.domain x
  candidate_contained :
    forall eps k (hk : k < (choosePartition eps).pieces) x
      (_ : ((choosePartition eps).cell k hk).contains x),
      QInterval.ContainsInterval
        (derivativeBound eps k)
        (dF.compute x (chooseStage eps))
  local_endpoint_contained :
    forall eps k (hk : k < (choosePartition eps).pieces),
      QInterval.ContainsInterval
        (((choosePartition eps).cell k hk).scaleBound
          (derivativeBound eps k))
        (endpointDifferenceInterval F
          ((choosePartition eps).cell k hk).lower
          ((choosePartition eps).cell k hk).upper
          (chooseStage eps))
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k _ => derivativeBound eps k)).width <= eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseStage eps)).width <= eps.val

def SelectedStageCandidateDerivativeFTCIndexed.toSelected
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTCIndexed F dF a b) :
    SelectedStageCandidateDerivativeFTC F dF a b where
  primitive_valid := h.primitive_valid
  choosePartition := h.choosePartition
  chooseStage := h.chooseStage
  derivativeBound := fun eps k _ => h.derivativeBound eps k
  primitive_domain_on := h.primitive_domain_on
  candidate_domain_on := h.candidate_domain_on
  candidate_contained := h.candidate_contained
  local_endpoint_contained := h.local_endpoint_contained
  riemann_width := by
    intro eps
    simpa using h.riemann_width eps
  endpoint_width := h.endpoint_width

theorem selectedStageCandidateDerivativeFTCIndexed
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTCIndexed F dF a b) :
    h.toSelected.boundedIntegralRaw.Equiv h.toSelected.endpointRaw := by
  exact SelectedStageCandidateDerivativeFTC.equiv_endpoint h.toSelected

/-- Top-level closure theorem for the stage-indexed candidate-derivative
strategy. -/
theorem selectedStageCandidateDerivativeFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw :=
  h.equiv_endpoint

/-- A finite candidate-derivative FTC certificate with independently chosen
derivative and primitive-endpoint evaluation stages.

The two schedules are intentional.  A step-aware derivative construction can
need a fine stage depending on a cell width in order to enclose the primitive
secant, while epsilon--delta continuity can provide a different common stage
at which the candidate derivative is enclosed throughout that cell.  The
finite telescope only needs all *endpoint* boxes at one common stage, so
requiring those two unrelated schedules to coincide would add a spurious
analytic obligation.

As in `SelectedStageCandidateDerivativeFTC`, the certificate is finite at
each requested outer precision: its partition, both stages, cell bounds, and
all enclosures are explicit rational data. -/
structure TwoStageCandidateDerivativeFTC
    (F dF : RealFunRaw) (a b : Rat) where
  primitive_valid : F.Valid
  choosePartition : QPos -> RationalPartition a b
  chooseDerivativeStage : QPos -> Nat
  chooseEndpointStage : QPos -> Nat
  derivativeBound :
    forall eps,
      forall k (_ : k < (choosePartition eps).pieces), QInterval
  primitive_domain_on :
    forall eps i, i <= (choosePartition eps).pieces ->
      F.domain ((choosePartition eps).point i)
  candidate_domain_on :
    forall eps k (hk : k < (choosePartition eps).pieces) x,
      ((choosePartition eps).cell k hk).contains x -> dF.domain x
  candidate_contained :
    forall eps k (hk : k < (choosePartition eps).pieces) x
      (_ : ((choosePartition eps).cell k hk).contains x),
      QInterval.ContainsInterval
        (derivativeBound eps k hk)
        (dF.compute x (chooseDerivativeStage eps))
  local_endpoint_contained :
    forall eps k (hk : k < (choosePartition eps).pieces),
      QInterval.ContainsInterval
        (((choosePartition eps).cell k hk).scaleBound (derivativeBound eps k hk))
        (endpointDifferenceInterval F
          ((choosePartition eps).cell k hk).lower
          ((choosePartition eps).cell k hk).upper
          (chooseEndpointStage eps))
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk => derivativeBound eps k hk)).width <= eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointStage eps)).width <= eps.val

namespace TwoStageCandidateDerivativeFTC

/-- The finite derivative-bound sum selected at an outer precision. -/
def boundedIntegralInterval
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) (eps : QPos) : QInterval :=
  (h.choosePartition eps).boundIntegralSum
    (fun k hk => h.derivativeBound eps k hk)

/-- The primitive endpoint box, evaluated at its independently selected
common stage. -/
def endpointInterval
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) (eps : QPos) : QInterval :=
  endpointDifferenceInterval F a b (h.chooseEndpointStage eps)

/-- The literal finite telescope still derives overlap: only the endpoint
stage participates in the telescoping calculation. -/
theorem overlap
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) (eps : QPos) :
    QInterval.Overlaps (h.boundedIntegralInterval eps) (h.endpointInterval eps) := by
  apply RationalPartition.boundIntegralSum_overlaps_endpointDifference
    (P := h.choosePartition eps) (F := F) (prec := h.chooseEndpointStage eps)
    h.primitive_valid
  · intro i hi
    exact h.primitive_domain_on eps i hi
  · intro k hk
    simpa [RationalPartition.cell] using h.local_endpoint_contained eps k hk

theorem closeAt
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) (eps : QPos) :
    QInterval.CloseAt (h.boundedIntegralInterval eps) (h.endpointInterval eps) eps := by
  exact ⟨h.overlap eps, h.riemann_width eps, h.endpoint_width eps⟩

def boundedIntegralCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) : Nat -> QInterval :=
  fun n => h.boundedIntegralInterval (precisionAtStage n)

def endpointCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) : Nat -> QInterval :=
  fun n => h.endpointInterval (precisionAtStage n)

def boundedIntegralRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) : RealCompute where
  compute := h.boundedIntegralCompute

def endpointRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) : RealCompute where
  compute := h.endpointCompute

/-- The two independently scheduled finite algorithms compute the same raw
real: the derivative schedule affects the certified cell bounds, while the
endpoint schedule supplies the common-stage telescope. -/
theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hgood := h.closeAt (precisionAtStage n)
  exact (RealCompute.compareAt_overlap_iff
    h.boundedIntegralRaw h.endpointRaw n n).2 hgood.1

end TwoStageCandidateDerivativeFTC

/-- Top-level closure theorem for the independently scheduled finite
candidate-derivative strategy. -/
theorem twoStageCandidateDerivativeFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw :=
  h.equiv_endpoint

/-- A common-stage certificate is a special case of the two-stage interface.
This preserves the simpler API for constructions whose derivative and
endpoint schedules genuinely coincide. -/
def SelectedStageCandidateDerivativeFTC.toTwoStage
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) :
    TwoStageCandidateDerivativeFTC F dF a b where
  primitive_valid := h.primitive_valid
  choosePartition := h.choosePartition
  chooseDerivativeStage := h.chooseStage
  chooseEndpointStage := h.chooseStage
  derivativeBound := h.derivativeBound
  primitive_domain_on := h.primitive_domain_on
  candidate_domain_on := h.candidate_domain_on
  candidate_contained := h.candidate_contained
  local_endpoint_contained := h.local_endpoint_contained
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width

inductive MonotonicityKind where
  | nondecreasing
  | nonincreasing
deriving DecidableEq, Repr

def endpointDerivativeBound
    (kind : MonotonicityKind) (dF : RealFunRaw)
    {a b : Rat} (C : RationalSubinterval a b) (prec : Nat) : QInterval :=
  match kind with
  | .nondecreasing =>
      { lo := (dF.compute C.lower prec).lo,
        hi := (dF.compute C.upper prec).hi }
  | .nonincreasing =>
      { lo := (dF.compute C.upper prec).lo,
        hi := (dF.compute C.lower prec).hi }

/-- A common way to produce a derivative bound: prove the derivative is
monotone on the short cell, then use endpoint derivative enclosures as the
range bound. -/
structure MonotoneDerivativeBoundMethod
    (dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  kind : MonotonicityKind
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> dF.domain x
  endpoint_bound_ordered :
    forall n, 0 <= (endpointDerivativeBound kind dF C (evalPrecision n)).width
  endpoint_contains_values :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (endpointDerivativeBound kind dF C (evalPrecision n))
        (dF.compute x (evalPrecision n))

namespace MonotoneDerivativeBoundMethod

def toDerivativeBound
    {dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (M : MonotoneDerivativeBoundMethod dF C) :
    DerivativeBoundOnSubinterval dF C where
  bound := fun n => endpointDerivativeBound M.kind dF C (M.evalPrecision n)
  evalPrecision := M.evalPrecision
  domain_on := M.domain_on
  bound_ordered := M.endpoint_bound_ordered
  contains_values := M.endpoint_contains_values

end MonotoneDerivativeBoundMethod

inductive CurvatureKind where
  | convex
  | concave
deriving DecidableEq, Repr

namespace CurvatureKind

def derivativeMonotonicity : CurvatureKind -> MonotonicityKind
  | .convex => .nondecreasing
  | .concave => .nonincreasing

end CurvatureKind

def secantSlopeIntervalOfRealFun
    (F : RealFunRaw) (x y : Rat) (prec : Nat) : QInterval :=
  QInterval.slopeBetween (F.compute y prec) (F.compute x prec) (y - x)

/-- Later endpoint stages produce a nested secant enclosure.  This is the
stage-coherence theorem for the finite secant algorithm; it uses only the
endpoint nesting supplied by `RealFunRaw.Valid`. -/
theorem secantSlopeIntervalOfRealFun_contains_later
    {F : RealFunRaw} (hF : F.Valid)
    {x y : Rat} (hx : F.domain x) (hy : F.domain y) (hxy : x < y)
    {n m : Nat} (hnm : n <= m) :
    QInterval.ContainsInterval
      (secantSlopeIntervalOfRealFun F x y n)
      (secantSlopeIntervalOfRealFun F x y m) := by
  have hxn := (hF x hx).2.1 n m hnm
  have hyn := (hF y hy).2.1 n m hnm
  have hstep : 0 < y - x := by
    rw [← Rat.lt_iff_sub_pos]
    exact hxy
  apply QInterval.slopeBetween_contains_of_pos hstep
  · exact ⟨hyn.1, hyn.2.2⟩
  · exact ⟨hxn.1, hxn.2.2⟩

/-- Rational secant-slope formulation of convexity/concavity on a short cell.

This is a helper certificate for producing derivative bounds.  The FTC layer
above only consumes `DerivativeBoundOnSubinterval`; it does not depend on this
curvature data directly. -/
structure CurvatureOnSubinterval
    (F : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  kind : CurvatureKind
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> F.domain x
  secant_slope_order :
    forall n w x y z,
      C.contains w ->
      C.contains x ->
      C.contains y ->
      C.contains z ->
      w < x ->
      x <= y ->
      y < z ->
        match kind with
        | .convex =>
            QInterval.WeakLe
              (secantSlopeIntervalOfRealFun F w x (evalPrecision n))
              (secantSlopeIntervalOfRealFun F y z (evalPrecision n))
        | .concave =>
            QInterval.WeakLe
              (secantSlopeIntervalOfRealFun F y z (evalPrecision n))
              (secantSlopeIntervalOfRealFun F w x (evalPrecision n))

/-- Evidence that a derivative bound was obtained through a curvature
argument: convexity supplies nondecreasing derivative bounds, concavity supplies
nonincreasing derivative bounds.  The result fed to FTC is still just
`toDerivativeBound`. -/
structure DerivativeBoundFromCurvature
    (F dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  curvature : CurvatureOnSubinterval F C
  monotoneDerivative : MonotoneDerivativeBoundMethod dF C
  compatible :
    monotoneDerivative.kind = curvature.kind.derivativeMonotonicity

namespace DerivativeBoundFromCurvature

def toDerivativeBound
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : DerivativeBoundFromCurvature F dF C) :
    DerivativeBoundOnSubinterval dF C :=
  H.monotoneDerivative.toDerivativeBound

end DerivativeBoundFromCurvature

/-- Curvature-facing FTC certificate.

This is the finite certificate-shaped route for primitives whose derivative
bounds come from curvature on each rational partition cell.  It handles both
convex and concave cells: the curvature kind determines whether endpoint
derivative bounds are nondecreasing or nonincreasing, and the result fed to the
FTC layer is still just a derivative-bound certificate. -/
structure CurvatureFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  curvatureBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((curvatureBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((curvatureBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((curvatureBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace CurvatureFTCCertificate

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  derivativeBound := fun eps k hk => (h.curvatureBound eps k hk).toDerivativeBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end CurvatureFTCCertificate

/-- Convexity-facing FTC certificate.

This is the current finite certificate-shaped route: convexity supplies
monotone derivative bounds on rational partition cells, and those local
bounds feed the general `DerivativeBoundFTC` endpoint bridge.

The later one-sided convex FTC should construct this certificate from exact
convexity, one-sided derivative data, monotone integrability, and telescoping
secant inequalities. -/
structure ConvexFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  convexBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  convex_kind :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        (convexBound eps k hk).curvature.kind = CurvatureKind.convex
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((convexBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((convexBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((convexBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

/-- Backward-compatible name for the older blueprint/API wording. -/
abbrev LegacyConvexFTC (F dF : RealFunRaw) (a b : Rat) :=
  ConvexFTCCertificate F dF a b

namespace ConvexFTCCertificate

def toCurvatureFTCCertificate
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    CurvatureFTCCertificate F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  curvatureBound := h.convexBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b :=
  h.toCurvatureFTCCertificate.toDerivativeBoundFTC

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end ConvexFTCCertificate

/-- Concavity-facing FTC certificate.

This is the mirror of `ConvexFTCCertificate`.  It is the named finite
certificate route for primitives, such as arctangent on `[0,1]`, whose
curvature makes the derivative nonincreasing on each rational partition cell.
The certificate still feeds the same curvature and derivative-bound FTC
machinery. -/
structure ConcaveFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  concaveBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  concave_kind :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        (concaveBound eps k hk).curvature.kind = CurvatureKind.concave
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((concaveBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((concaveBound eps k hk).toDerivativeBound).bound
            (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((concaveBound eps k hk).toDerivativeBound).bound
              (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace ConcaveFTCCertificate

def toCurvatureFTCCertificate
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    CurvatureFTCCertificate F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  curvatureBound := h.concaveBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b :=
  h.toCurvatureFTCCertificate.toDerivativeBoundFTC

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end ConcaveFTCCertificate

/- Legacy namespace aliases retained for existing references. -/
namespace LegacyConvexFTC

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    DerivativeBoundFTC F dF a b :=
  ConvexFTCCertificate.toDerivativeBoundFTC h

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  ConvexFTCCertificate.equiv_endpoint h

end LegacyConvexFTC

/-- Compatibility theorem for the old convexity-facing FTC name.

Once a convexity certificate has produced derivative bounds on the chosen
rational partition cells, the finite FTC conclusion is exactly the
derivative-bound endpoint equivalence. -/
theorem legacyConvexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Completed convexity-facing FTC bridge used by the integral chapter.

This is currently the derivative-bound formulation: convexity supplies the
local monotone derivative bounds, and the general derivative-bound FTC returns
endpoint equivalence for the integral raw real. -/
theorem convexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Completed concavity-facing FTC bridge used by the arctangent-integral
route. -/
theorem concaveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Curvature-facing FTC bridge.  This is the version useful for both convex
and concave primitives, including the arctangent primitive on the unit
interval. -/
theorem curvatureFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- A partial function together with a proof that it is defined at every
rational point of a closed rational interval.

This rules out visible rational-domain failures, such as `1/x` on an interval
containing `0`.  It does not by itself rule out a hidden irrational singularity
such as `1 / (x^2 - 2)` on `[1,2]`, because every rational point of `[1,2]`
is still in the pointwise domain.  That stronger exclusion is the job of
`IntervalRegularOn` below. -/
structure FunctionOnInterval where
  raw : PartialRealFunRaw
  lower : Rat
  upper : Rat
  defined_on : forall x, inDomainInterval lower upper x -> raw.definedAt x
  valid_on : forall x h, RealCompute.ValidCompute (raw.compute x h)

namespace FunctionOnInterval

/-! Construct an interval function from an evaluator whose computation is
independent of the proof that the input lies in the interval. -/
def ofStable
    (f : StablePartialRealFunRaw)
    (a b : Rat)
    (defined_on : forall x, inDomainInterval a b x -> f.definedAt x)
    (valid_on : forall x, f.definedAt x ->
      RealCompute.ValidCompute (f.compute x)) : FunctionOnInterval where
  raw := f.toPartial
  lower := a
  upper := b
  defined_on := defined_on
  valid_on := by
    intro x hx
    change RealCompute.ValidCompute (f.compute x)
    exact valid_on x hx

def compute (F : FunctionOnInterval) (x : Rat) (hx : inDomainInterval F.lower F.upper x)
    (n : Nat) : QInterval :=
  F.raw.compute x (F.defined_on x hx) n

@[simp] theorem ofStable_compute
    (f : StablePartialRealFunRaw)
    (a b : Rat)
    (defined_on : forall x, inDomainInterval a b x -> f.definedAt x)
    (valid_on : forall x, f.definedAt x ->
      RealCompute.ValidCompute (f.compute x))
    (x : Rat) (hx : inDomainInterval a b x) (n : Nat) :
    (ofStable f a b defined_on valid_on).compute x hx n = f.compute x n := rfl

/-- A rational-valued formula, viewed as an exact interval function on a
closed rational interval.

This is the standard wrapper for compactified rational densities.  It only
certifies the pointwise evaluator: continuity and integral constructions
remain separate finite obligations. -/
def exactRat (f : Rat -> Rat) (a b : Rat) : FunctionOnInterval where
  raw :=
    { definedAt := fun _ => True
      compute := fun x _ _ => { lo := f x, hi := f x } }
  lower := a
  upper := b
  defined_on := fun _ _ => trivial
  valid_on := by
    intro x _hx
    simpa using RealCompute.ofRat_valid (f x)

theorem exactRat_compute (f : Rat -> Rat) (a b x : Rat)
    (hx : inDomainInterval a b x) (n : Nat) :
    (exactRat f a b).compute x hx n = { lo := f x, hi := f x } :=
  rfl

/-! Pointwise addition on a common rational interval.

This is the interval-level counterpart of `RealFunRaw.add`.  The domain
agreement is explicit because interval functions carry their rational chart;
the validity proof is inherited from the additive closure of `RealCompute`. -/
def add
    (F G : FunctionOnInterval)
    (same_lower : F.lower = G.lower)
    (same_upper : F.upper = G.upper) : FunctionOnInterval where
  raw :=
    { definedAt := fun x =>
        inDomainInterval F.lower F.upper x /\
          F.raw.definedAt x /\ G.raw.definedAt x
      compute := fun x hx n =>
        QInterval.addInterval
          (F.raw.compute x hx.2.1 n)
          (G.raw.compute x hx.2.2 n) }
  lower := F.lower
  upper := F.upper
  defined_on := by
    intro x hx
    refine ⟨hx, F.defined_on x hx, G.defined_on x ?_⟩
    constructor
    · rw [← same_lower]
      exact hx.1
    · rw [← same_upper]
      exact hx.2
  valid_on := by
    intro x hx
    let hxF : inDomainInterval F.lower F.upper x := hx.1
    let hxG : inDomainInterval G.lower G.upper x := by
      constructor
      · rw [← same_lower]
        exact hxF.1
      · rw [← same_upper]
        exact hxF.2
    let X : RealCompute := { compute := F.raw.compute x hx.2.1 }
    let Y : RealCompute := { compute := G.raw.compute x hx.2.2 }
    have hX : X.Valid := by
      simpa [X, RealCompute.Valid] using F.valid_on x hx.2.1
    have hY : Y.Valid := by
      simpa [Y, RealCompute.Valid] using G.valid_on x hx.2.2
    have hsum := RealCompute.add_valid hX hY
    change RealCompute.ValidCompute
      (fun n => QInterval.addInterval
        (F.raw.compute x hx.2.1 n)
        (G.raw.compute x hx.2.2 n))
    change RealCompute.ValidCompute (RealCompute.addCompute X Y) at hsum
    exact hsum

@[simp] theorem add_compute
    (F G : FunctionOnInterval)
    (same_lower : F.lower = G.lower)
    (same_upper : F.upper = G.upper)
    (x : Rat) (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    (add F G same_lower same_upper).compute x
      (by simpa [add] using
        (show inDomainInterval F.lower F.upper x from hx)) n =
      QInterval.addInterval (F.compute x hx n)
        (G.compute x (by
          constructor
          · rw [← same_lower]
            exact hx.1
          · rw [← same_upper]
            exact hx.2) n) := by
  rfl

/-- The pointwise interval product of two functions on the same rational
interval, under explicit nonnegative rational bounds for both factors.

This is an evaluator-level construction.  It intentionally supplies neither
a product-derivative theorem nor an integral construction: those require
separate finite certificates. -/
def mulOfNonnegBounded
    (F G : FunctionOnInterval)
    (same_lower : F.lower = G.lower) (same_upper : F.upper = G.upper)
    (Fbounds : forall x (hx : inDomainInterval F.lower F.upper x),
      Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (F.compute x hx n).lo /\ (F.compute x hx n).hi <= B)
    (Gbounds : forall x (hx : inDomainInterval G.lower G.upper x),
      Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (G.compute x hx n).lo /\ (G.compute x hx n).hi <= B) :
    FunctionOnInterval where
  raw :=
    { definedAt := fun x =>
        inDomainInterval F.lower F.upper x /\
          F.raw.definedAt x /\ G.raw.definedAt x
      compute := fun x hx n =>
        QBox.mulRealInterval
          (F.raw.compute x hx.2.1 n).lo (F.raw.compute x hx.2.1 n).hi
          (G.raw.compute x hx.2.2 n).lo (G.raw.compute x hx.2.2 n).hi }
  lower := F.lower
  upper := F.upper
  defined_on := by
    intro x hx
    refine ⟨hx, F.defined_on x hx, G.defined_on x ?_⟩
    constructor
    · rw [← same_lower]
      exact hx.1
    · rw [← same_upper]
      exact hx.2
  valid_on := by
    intro x hx
    let hxF : inDomainInterval F.lower F.upper x := hx.1
    let hxG : inDomainInterval G.lower G.upper x := by
      constructor
      · rw [← same_lower]
        exact hxF.1
      · rw [← same_upper]
        exact hxF.2
    rcases Fbounds x hxF with ⟨BF, hBF, hFbounds⟩
    rcases Gbounds x hxG with ⟨BG, hBG, hGbounds⟩
    let X : RealCompute := { compute := F.raw.compute x hx.2.1 }
    let Y : RealCompute := { compute := G.raw.compute x hx.2.2 }
    have hX : X.Valid := by
      simpa [X, RealCompute.Valid] using F.valid_on x hx.2.1
    have hY : Y.Valid := by
      simpa [Y, RealCompute.Valid] using G.valid_on x hx.2.2
    have hXbounds : forall n,
        0 <= (X.compute n).lo /\ (X.compute n).hi <= BF := by
      intro n
      have hproof : F.defined_on x hxF = hx.2.1 := Subsingleton.elim _ _
      simpa [X, FunctionOnInterval.compute, hproof] using hFbounds n
    have hYbounds : forall n,
        0 <= (Y.compute n).lo /\ (Y.compute n).hi <= BG := by
      intro n
      have hproof : G.defined_on x hxG = hx.2.2 := Subsingleton.elim _ _
      simpa [Y, FunctionOnInterval.compute, hproof] using hGbounds n
    have hproduct : (X * Y).Valid :=
      RealCompute.mul_valid_of_nonneg_bounded
        hX hY hBF hBG hXbounds hYbounds
    change RealCompute.ValidCompute (RealCompute.mulCompute X Y) at hproduct
    change RealCompute.ValidCompute (RealCompute.mulCompute X Y)
    exact hproduct

@[simp] theorem mulOfNonnegBounded_compute
    (F G : FunctionOnInterval)
    (same_lower : F.lower = G.lower) (same_upper : F.upper = G.upper)
    (Fbounds : forall x (hx : inDomainInterval F.lower F.upper x),
      Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (F.compute x hx n).lo /\ (F.compute x hx n).hi <= B)
    (Gbounds : forall x (hx : inDomainInterval G.lower G.upper x),
      Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (G.compute x hx n).lo /\ (G.compute x hx n).hi <= B)
    (x : Rat) (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    (mulOfNonnegBounded F G same_lower same_upper Fbounds Gbounds).compute x hx n =
      QBox.mulRealInterval
        (F.compute x hx n).lo (F.compute x hx n).hi
        (G.compute x (by
          constructor
          · rw [← same_lower]
            exact hx.1
          · rw [← same_upper]
            exact hx.2) n).lo
        (G.compute x (by
          constructor
          · rw [← same_lower]
            exact hx.1
          · rw [← same_upper]
            exact hx.2) n).hi := by
  rfl

def secantSlopeInterval (F : FunctionOnInterval)
    (x y : Rat)
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y)
    (n : Nat) : QInterval :=
  QInterval.slopeBetween (F.compute y hy n) (F.compute x hx n) (y - x)

/-- Restrict an interval-certified function to a smaller rational interval. -/
def restrict (F : FunctionOnInterval) (a b : Rat)
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    FunctionOnInterval where
  raw := F.raw
  lower := a
  upper := b
  defined_on := by
    intro x hx
    exact F.defined_on x
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
  valid_on := by
    intro x hx
    exact F.valid_on x hx

/-- Pointwise sum relation for interval-certified functions on the same
rational interval.  This is a theorem-facing relation: it records that `H`
represents `F + G` on the common interval, without choosing a particular
implementation of the sum evaluator. -/
def PointwiseAdd (F G H : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  F.lower = H.lower /\ F.upper = H.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x)
    (hxH : inDomainInterval H.lower H.upper x),
      (H.raw.evalRaw x (H.defined_on x hxH)).Equiv
        ((F.raw.evalRaw x (F.defined_on x hxF)) +
          (G.raw.evalRaw x (G.defined_on x hxG)))

/-- Pointwise rational-scalar relation for interval-certified functions. -/
def PointwiseScaleRat (r : Rat) (F G : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x),
      (G.raw.evalRaw x (G.defined_on x hxG)).Equiv
        (RealCompute.scaleRat r
          (F.raw.evalRaw x (F.defined_on x hxF)))

/-- Pointwise order relation for interval-certified functions on the same
rational interval.  This is the order analogue of `PointwiseAdd`: it records
the theorem-facing fact that `F(x) <= G(x)` for every rational point in the
common interval. -/
def PointwiseLe (F G : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x),
      (F.raw.evalRaw x (F.defined_on x hxF)).Le
        (G.raw.evalRaw x (G.defined_on x hxG))

end FunctionOnInterval

namespace Integral

/-- A valid numerical candidate associated with an interval function.

This deliberately carries NO claim that the value is the integral of `F`.
The `F` parameter alone supplies no semantic evidence. The mathematical
specification is `Integral.HasIntegral` in `IntegralSpecification`; its
`ConstructionFor` additionally requires that semantic proof. Existing finite
algorithms use this lower-level package before their semantic bridge is proved.
-/
structure CandidateConstructionFor (F : FunctionOnInterval) where
  compute : Nat -> QInterval
  certificate : RealCompute.ValidCompute compute

def candidateValueFor (F : FunctionOnInterval) (c : CandidateConstructionFor F) : RealCompute where
  compute := c.compute

theorem candidateValueFor_compute_eq (F : FunctionOnInterval)
    (c : CandidateConstructionFor F) (n : Nat) :
    (candidateValueFor F c).compute n = c.compute n := rfl

theorem candidateValueFor_valid (F : FunctionOnInterval)
    (c : CandidateConstructionFor F) :
    (candidateValueFor F c).Valid :=
  c.certificate

/-! Finite sums of raw representatives are the algebraic core of piecewise
integral assembly.  Keeping this operation explicit lets an adjacent
interval or multi-turn proof concatenate certified pieces before it proves
anything about a limiting schedule. -/

def finiteRawSum : List RealCompute -> RealCompute
  | [] => RealCompute.zero
  | x :: xs => x + finiteRawSum xs

theorem finiteRawSum_valid :
    ∀ xs : List RealCompute, (∀ x ∈ xs, x.Valid) -> (finiteRawSum xs).Valid
  | [], _ => by
      change (RealCompute.ofRat 0).Valid
      exact RealCompute.ofRat_valid 0
  | x :: xs, hxs => by
      have hx : x.Valid := hxs x (by simp)
      have htail : ∀ y ∈ xs, y.Valid := by
        intro y hy
        exact hxs y (by simp [hy])
      simpa [finiteRawSum] using
        RealCompute.add_valid hx (finiteRawSum_valid xs htail)

theorem finiteRawSum_append_equiv
    (xs ys : List RealCompute)
    (hxs : ∀ x ∈ xs, x.Valid)
    (hys : ∀ y ∈ ys, y.Valid) :
    (finiteRawSum (xs ++ ys)).Equiv
      (finiteRawSum xs + finiteRawSum ys) := by
  induction xs with
  | nil =>
      simpa [finiteRawSum] using
        (RealCompute.equiv_symm
          (RealCompute.zero_add_equiv (finiteRawSum_valid ys hys)))
  | cons x xs ih =>
      have hx : x.Valid := hxs x (by simp)
      have htail : ∀ z ∈ xs, z.Valid := by
        intro z hz
        exact hxs z (by simp [hz])
      have hsum : (finiteRawSum (xs ++ ys)).Valid :=
        finiteRawSum_valid (xs ++ ys) (by
          intro z hz
          simp only [List.mem_append] at hz
          exact hz.elim (fun hz' => hxs z (by simp [hz']))
            (fun hz' => hys z hz'))
      have hleft : (finiteRawSum xs).Valid := finiteRawSum_valid xs htail
      have hright : (finiteRawSum ys).Valid := finiteRawSum_valid ys hys
      have hih := ih htail
      have hadd : (finiteRawSum xs + finiteRawSum ys).Valid :=
        RealCompute.add_valid hleft hright
      have hassoc := RealCompute.add_assoc_equiv x
        (finiteRawSum xs) (finiteRawSum ys) hx hleft hright
      have htransport :
          (x + finiteRawSum (xs ++ ys)).Equiv
            (x + (finiteRawSum xs + finiteRawSum ys)) := by
        exact RealCompute.add_equiv
          hx hx hsum hadd (RealCompute.equiv_refl x hx) hih
      apply RealCompute.equiv_trans
        (RealCompute.add_valid hx hsum)
        (RealCompute.add_valid hx hadd)
        (RealCompute.add_valid (RealCompute.add_valid hx hleft) hright)
        htransport
        (RealCompute.equiv_symm hassoc)

/-! Finite raw sums preserve the exact interval order supplied cell by cell.
This is the algebraic core of lower/upper rectangle comparison; it does not
require a limiting argument or a completed-real order. -/
inductive FiniteRawListLe : List RealCompute -> List RealCompute -> Prop where
  | nil : FiniteRawListLe [] []
  | cons {x y : RealCompute} {xs ys : List RealCompute} :
      x.Le y -> FiniteRawListLe xs ys -> FiniteRawListLe (x :: xs) (y :: ys)

theorem FiniteRawListLe.refl {xs : List RealCompute}
    (hvalid : forall x, x ∈ xs -> x.Valid) :
    FiniteRawListLe xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      apply FiniteRawListLe.cons
      · exact RealCompute.le_refl x (hvalid x (by simp))
      · apply ih
        intro y hy
        exact hvalid y (by simp [hy])

inductive FiniteRawListEquiv : List RealCompute -> List RealCompute -> Prop where
  | nil : FiniteRawListEquiv [] []
  | cons {x y : RealCompute} {xs ys : List RealCompute} :
      x.Equiv y -> FiniteRawListEquiv xs ys ->
        FiniteRawListEquiv (x :: xs) (y :: ys)

theorem FiniteRawListEquiv.refl {xs : List RealCompute}
    (hvalid : forall x, x ∈ xs -> x.Valid) :
    FiniteRawListEquiv xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      apply FiniteRawListEquiv.cons
      · exact RealCompute.equiv_refl x (hvalid x (by simp))
      · apply ih
        intro y hy
        exact hvalid y (by simp [hy])

theorem FiniteRawListEquiv.symm
    {xs ys : List RealCompute} :
    FiniteRawListEquiv xs ys -> FiniteRawListEquiv ys xs
  | .nil => .nil
  | .cons hhead htail =>
      .cons (RealCompute.equiv_symm hhead) (FiniteRawListEquiv.symm htail)

theorem finiteRawSum_equiv_of_forall
    {xs ys : List RealCompute}
    (hxy : FiniteRawListEquiv xs ys)
    (hxs : forall x, x ∈ xs -> x.Valid)
    (hys : forall y, y ∈ ys -> y.Valid) :
    (finiteRawSum xs).Equiv (finiteRawSum ys) := by
  induction hxy with
  | nil =>
      exact RealCompute.equiv_refl RealCompute.zero (by
        change RealCompute.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
        exact RealCompute.ofRat_valid 0)
  | @cons x y xs ys hhead htail ih =>
      have hx : x.Valid := hxs x (by simp)
      have hy : y.Valid := hys y (by simp)
      have hxs' : forall z, z ∈ xs -> z.Valid := by
        intro z hz
        exact hxs z (by simp [hz])
      have hys' : forall z, z ∈ ys -> z.Valid := by
        intro z hz
        exact hys z (by simp [hz])
      have hleft : (finiteRawSum xs).Valid :=
        finiteRawSum_valid xs hxs'
      have hright : (finiteRawSum ys).Valid :=
        finiteRawSum_valid ys hys'
      have htail' := ih hxs' hys'
      simpa [finiteRawSum] using
        (RealCompute.add_equiv hx hy hleft hright hhead htail')

theorem finiteRawSum_le_of_forall₂
    {xs ys : List RealCompute}
    (hxy : FiniteRawListLe xs ys) :
    (finiteRawSum xs).Le (finiteRawSum ys) := by
  induction hxy with
  | nil =>
      change RealCompute.zero.Le RealCompute.zero
      exact RealCompute.le_refl RealCompute.zero (by
        change RealCompute.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
        exact RealCompute.ofRat_valid 0)
  | cons hhead htail ih =>
      change (RealCompute.add _ (finiteRawSum _)).Le
        (RealCompute.add _ (finiteRawSum _))
      exact RealCompute.le_add_le_add hhead ih

/-! Pure finite telescoping for raw endpoint values.  This theorem is kept
independent of interval domains and partition bookkeeping; callers transport
their adjacent endpoint evaluators into this list algebra first. -/
def rawLast (x : RealCompute) : List RealCompute -> RealCompute
  | [] => x
  | y :: ys => rawLast y ys

def rawAdjacentDifferenceList : List RealCompute -> List RealCompute
  | [] => []
  | x :: [] => []
  | x :: y :: ys => (y - x) :: rawAdjacentDifferenceList (y :: ys)

theorem rawAdjacentDifferenceList_length (xs : List RealCompute) :
    (rawAdjacentDifferenceList xs).length = xs.length - 1 := by
  induction xs with
  | nil => simp [rawAdjacentDifferenceList]
  | cons x xs ih =>
      cases xs with
      | nil => simp [rawAdjacentDifferenceList]
      | cons y ys =>
          simp only [rawAdjacentDifferenceList, List.length_cons]
          simp only [List.length_cons] at ih
          omega

theorem RealCompute.sub_self_equiv_zero {x : RealCompute} (hx : x.Valid) :
    (x - x).Equiv RealCompute.zero := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have ho := RealCompute.interval_order_of_valid x hx n
  apply (RealCompute.compareAt_overlap_iff (x - x) RealCompute.zero n n).2
  change QInterval.Overlaps (RealCompute.subCompute x x n) (RealCompute.zero.compute n)
  unfold RealCompute.subCompute RealCompute.zero RealCompute.ofRat QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem rawLast_valid {x : RealCompute} {xs : List RealCompute}
    (hvalid : forall y, y ∈ x :: xs -> y.Valid) :
    (rawLast x xs).Valid := by
  induction xs generalizing x with
  | nil => exact hvalid x (by simp)
  | cons y ys ih =>
      apply ih
      intro z hz
      exact hvalid z (by simp [hz])

theorem rawAdjacentDifferenceList_valid {xs : List RealCompute}
    (hvalid : forall x, x ∈ xs -> x.Valid) :
    forall y, y ∈ rawAdjacentDifferenceList xs -> y.Valid := by
  induction xs with
  | nil =>
      intro y hy
      simp [rawAdjacentDifferenceList] at hy
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro y hy
          simp [rawAdjacentDifferenceList] at hy
      | cons z zs =>
          intro y hy
          simp only [rawAdjacentDifferenceList, List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact RealCompute.sub_valid
              (hvalid z (by simp)) (hvalid x (by simp))
          · exact ih (fun w hw => hvalid w (by simp [hw])) y hy

theorem finiteRawSum_rawAdjacentDifferenceList_equiv_last_sub_first
    {x : RealCompute} {xs : List RealCompute}
    (hvalid : forall y, y ∈ x :: xs -> y.Valid) :
    (finiteRawSum (rawAdjacentDifferenceList (x :: xs))).Equiv
      (rawLast x xs - x) := by
  induction xs generalizing x with
  | nil =>
      have hx : x.Valid := hvalid x (by simp)
      simpa [rawAdjacentDifferenceList, rawLast, finiteRawSum] using
        (RealCompute.equiv_symm (RealCompute.sub_self_equiv_zero hx))
  | cons y ys ih =>
      have hx : x.Valid := hvalid x (by simp)
      have hy : y.Valid := hvalid y (by simp)
      have htail : forall z, z ∈ y :: ys -> z.Valid := by
        intro z hz
        exact hvalid z (by simp [hz])
      have hleft :
          (finiteRawSum (rawAdjacentDifferenceList (y :: ys))).Valid :=
        finiteRawSum_valid _
          (rawAdjacentDifferenceList_valid htail)
      have hhead : (y - x).Valid := RealCompute.sub_valid hy hx
      have hprev := ih htail
      have hlast : (rawLast y ys).Valid := rawLast_valid htail
      have hmiddle :
          ((y - x) + (rawLast y ys - y)).Valid :=
        RealCompute.add_valid hhead (RealCompute.sub_valid hlast hy)
      have htarget : (rawLast y ys - x).Valid :=
        RealCompute.sub_valid hlast hx
      have hadd :
          ((y - x) + finiteRawSum
            (rawAdjacentDifferenceList (y :: ys))).Equiv
            ((y - x) + (rawLast y ys - y)) := by
        exact RealCompute.add_equiv hhead hhead hleft
          (RealCompute.sub_valid hlast hy)
          (RealCompute.equiv_refl _ hhead) hprev
      have htel := RealCompute.sub_add_sub_cancel_middle_equiv hx hy hlast
      simpa [rawAdjacentDifferenceList, finiteRawSum, rawLast] using
        (RealCompute.equiv_trans
          (RealCompute.add_valid hhead hleft) hmiddle htarget hadd htel)

end Integral

namespace TwoStageCandidateDerivativeFTC

/-- The finite bounded-sum raw of any two-stage FTC certificate already
agrees with the canonical primitive endpoint raw.  No monotonicity of either
stage selector is needed for this comparison: at each requested stage the
finite telescope contains its selected endpoint box, and that box overlaps the
canonical endpoint box by the primitive's validated nestedness. -/
theorem boundedIntegralRaw_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    h.boundedIntegralRaw.Equiv (endpointDifferenceRaw F a b hendpoint) := by
  intro n
  let eps := precisionAtStage n
  let s := h.chooseEndpointStage eps
  have hcontains :
      QInterval.ContainsInterval
        ((h.choosePartition eps).boundIntegralSum (fun k hk => h.derivativeBound eps k hk))
        (endpointDifferenceInterval F a b s) := by
    apply RationalPartition.boundIntegralSum_contains_endpointDifference
      (P := h.choosePartition eps) (F := F) (prec := s) h.primitive_valid
    · intro i hi
      exact h.primitive_domain_on eps i hi
    · intro k hk
      simpa [RationalPartition.cell, s] using h.local_endpoint_contained eps k hk
  let endpoint : RealCompute := endpointDifferenceRaw F a b hendpoint
  have hvalid : endpoint.Valid := by
    simpa [endpoint, endpointDifferenceRaw, RealCompute.Valid] using hendpoint
  have hall := RealCompute.allStagesOverlap_refl endpoint hvalid s n
  have hover := (RealCompute.compareAt_overlap_iff endpoint endpoint s n).1 hall
  apply (RealCompute.compareAt_overlap_iff h.boundedIntegralRaw endpoint n n).2
  change QInterval.Overlaps
    ((h.choosePartition eps).boundIntegralSum (fun k hk => h.derivativeBound eps k hk))
    (endpointDifferenceCompute F a b n)
  have hscheduled :
      QInterval.Overlaps (endpointDifferenceInterval F a b s)
        (endpointDifferenceCompute F a b n) := by
    change QInterval.Overlaps
      (endpointDifferenceCompute F a b s)
      (endpointDifferenceCompute F a b n)
    simpa [endpoint, endpointDifferenceRaw] using hover
  exact ⟨Rat.le_trans hcontains.1 hscheduled.1,
    Rat.le_trans hscheduled.2 hcontains.2⟩

/-- Stabilize the actual finite bounded-sum evaluator of a two-stage FTC
certificate.  At runtime this reads only bounded-sum boxes and a rational
radius schedule; the primitive endpoint raw is used solely in the proof of
validity. -/
def stabilizedRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b)
    (_hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (radius : Nat -> Rat) : RealCompute :=
  RealCompute.prefixStabilize h.boundedIntegralRaw radius

/-- A width modulus for the finite sums and a covering, shrinking radius for
the canonical endpoint raw make the stabilized two-stage evaluator valid. -/
theorem stabilizedRaw_valid
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (radius : Nat -> Rat)
    (hshrink : RealCompute.WidthsShrinkToZero h.boundedIntegralRaw.compute)
    (hradius : forall n,
      ((endpointDifferenceRaw F a b hendpoint).compute n).width <= radius n)
    (hradius_shrinks : ShrinksToZero radius) :
    (h.stabilizedRaw hendpoint radius).Valid := by
  unfold stabilizedRaw
  exact RealCompute.prefixStabilize_valid hshrink
    (by simpa [endpointDifferenceRaw, RealCompute.Valid] using hendpoint)
    (h.boundedIntegralRaw_equiv_endpointDifference hendpoint)
    hradius hradius_shrinks

/-- The valid stabilized evaluator represents the primitive endpoint
difference. -/
theorem stabilizedRaw_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : TwoStageCandidateDerivativeFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (radius : Nat -> Rat)
    (hradius : forall n,
      ((endpointDifferenceRaw F a b hendpoint).compute n).width <= radius n) :
    (h.stabilizedRaw hendpoint radius).Equiv
      (endpointDifferenceRaw F a b hendpoint) := by
  unfold stabilizedRaw
  exact RealCompute.prefixStabilize_equiv_anchor
    (by simpa [endpointDifferenceRaw, RealCompute.Valid] using hendpoint)
    (h.boundedIntegralRaw_equiv_endpointDifference hendpoint)
    hradius

end TwoStageCandidateDerivativeFTC

def Integral.ExistsCandidateConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (Integral.CandidateConstructionFor F)

theorem integral_construction_proves_well_defined_for
    {F : FunctionOnInterval}
    (c : Integral.CandidateConstructionFor F) :
    Integral.ExistsCandidateConstructionFor F :=
  ⟨c⟩

/-- Epsilon-delta continuity stated entirely over rational inputs.

For a requested positive rational output tolerance `eps`, the certificate
chooses a positive rational input tolerance and one evaluation precision. Any
two rational points of the stated interval within that tolerance then have
output boxes within `eps` of one another, each of width at most `eps`.  This
is quantitative proximity, not literal overlap: a nonconstant function can
send nearby rational inputs to distinct exact rational values.  No topology,
completed real-valued function space, or implicit exact-value evaluation
occurs here.
`EffectiveModulusFor` below is the stronger computable-modulus presentation
used by the current calculus constructors. -/
def EpsilonDeltaContinuousOn (F : FunctionOnInterval) : Prop :=
  forall eps : QPos, Exists fun delta : QPos => Exists fun evalPrecision : Nat =>
    forall x y
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y),
      qabs (y - x) <= delta.val ->
        QInterval.NearAt
          (F.compute x hx evalPrecision)
          (F.compute y hy evalPrecision) eps

/-- Effective modulus for a partial function known to be defined on the whole
interval.  This is the continuity data used by IVT and eventually by the
integral constructor; it includes the domain certificate. -/
structure EffectiveModulusFor (F : FunctionOnInterval) where
  inputPrecision : Nat -> Nat
  evalPrecision : Nat -> Nat
  close :
    forall x y n
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y),
      qabs (y - x) <= (1 / ((inputPrecision n) : Rat)) ->
        intervalNearAtPrecision
          (F.compute x hx (evalPrecision n))
          (F.compute y hy (evalPrecision n))
          n

/-- Generic interval-level regularity.

This is the continuity notion we want calculus theorems to consume.  It does
not mention denominators or formulas.  It says that every sufficiently small
rational subinterval has a computable output interval, and that the output
interval can be made as narrow as requested.  A hidden singularity such as
`1 / (x^2 - 2)` on `[1,2]` should fail this condition, because arbitrarily
small rational subintervals can straddle the irrational pole. -/
structure IntervalRegularOn (F : FunctionOnInterval) where
  evalInterval : (I : QInterval) -> subintervalOf I F.lower F.upper -> Nat -> QInterval
  inputPrecision : Nat -> Nat
  inputPrecision_pos : forall n, 0 < inputPrecision n
  output_width :
    forall I hI n,
      I.width <= (1 / ((inputPrecision n) : Rat)) ->
        0 <= (evalInterval I hI n).width /\
        (evalInterval I hI n).width <= 1 / ((n + 1 : Nat) : Rat)
  contains_point_values :
    forall I hI x hx n,
      I.lo <= x ->
      x <= I.hi ->
        QInterval.ContainsInterval
        (evalInterval I hI n)
        (F.compute x hx n)

/-! A natural-number Lipschitz certificate on an arbitrary ordered rational chart. -/
def Integral.LipschitzOnIntervalNat (f : Rat -> Rat) (a b : Rat) (L : Nat) : Prop :=
  a <= b /\
  forall s t : Rat,
    a <= s -> s <= b -> a <= t -> t <= b ->
      qabs (f s - f t) <= (L : Rat) * qabs (t - s)

/-- Restrict a unit-chart Lipschitz certificate to any ordered rational
subinterval.  This is the finite transport used when one global estimate is
reused on the cells of a piecewise or turning-point integral. -/
theorem Integral.LipschitzOnIntervalNat.of_unit_subinterval
    (f : Rat -> Rat) (L : Nat) {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1)
    (hunit : Integral.LipschitzOnUnit f (L : Rat)) :
    Integral.LipschitzOnIntervalNat f a b L := by
  refine ⟨hab, ?_⟩
  intro s t hs hsb ht htb
  exact hunit.2 s t
    (Rat.le_trans ha hs) (Rat.le_trans hsb hb)
    (Rat.le_trans ha ht) (Rat.le_trans htb hb)

def IntervalRegularOn.of_lipschitzOnIntervalNat
    (f : Rat -> Rat) (a b : Rat) (L : Nat)
    (hlip : Integral.LipschitzOnIntervalNat f a b L) :
    IntervalRegularOn (FunctionOnInterval.exactRat f a b) where
  evalInterval := fun I _I _n =>
    { lo := f I.lo - (L : Rat) * I.width
      hi := f I.lo + (L : Rat) * I.width }
  inputPrecision := fun n => (2 * L + 1) * (n + 1)
  inputPrecision_pos := by
    intro n
    exact Nat.mul_pos (by omega) (Nat.succ_pos n)
  output_width := by
    intro I hI n hsmall
    have hL0 : 0 <= (L : Rat) := by exact_mod_cast Nat.zero_le L
    have hwidth : 0 <= I.width := by
      unfold QInterval.width
      grind [hI.2.1]
    have hscaled :
        (2 * (L : Rat)) * I.width <=
          (2 * (L : Rat)) /
            (((2 * L + 1) * (n + 1) : Nat) : Rat) := by
      have hscaled0 := Rat.mul_le_mul_of_nonneg_left hsmall
        (Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ 2) hL0)
      simpa [Rat.div_def, Rat.mul_assoc] using hscaled0
    have hden :
        (2 * (L : Rat)) /
            (((2 * L + 1) * (n + 1) : Nat) : Rat) <=
          1 / (((n + 1 : Nat) : Rat)) := by
      have hnpos : 0 < ((n + 1 : Nat) : Rat) :=
        (Rat.natCast_pos).2 (Nat.succ_pos n)
      have hfactor : 0 < (((2 * L + 1) * (n + 1) : Nat) : Rat) := by
        exact_mod_cast (Nat.mul_pos (by omega) (Nat.succ_pos n))
      apply Rat.le_of_mul_le_mul_right
        (c := (((2 * L + 1) * (n + 1) : Nat) : Rat) *
          ((n + 1 : Nat) : Rat))
      · rw [Rat.div_def, Rat.div_def]
        rw [show (((2 * L + 1) * (n + 1) : Nat) : Rat) =
          (2 * (L : Rat) + 1) * ((n + 1 : Nat) : Rat) by
            rw [Rat.natCast_mul, Rat.natCast_add, Rat.natCast_mul,
              Rat.natCast_add]
            grind]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      · exact Rat.mul_pos hfactor hnpos
    constructor
    · change 0 <=
        (f I.lo + (L : Rat) * I.width) -
          (f I.lo - (L : Rat) * I.width)
      have hnonneg : 0 <= (2 * (L : Rat)) * I.width :=
        Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hL0) hwidth
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
    · change
        (f I.lo + (L : Rat) * I.width) -
            (f I.lo - (L : Rat) * I.width) <=
          1 / (((n + 1 : Nat) : Rat))
      have hwidth_eq :
          (f I.lo + (L : Rat) * I.width) -
              (f I.lo - (L : Rat) * I.width) =
            (2 * (L : Rat)) * I.width := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      rw [hwidth_eq]
      exact Rat.le_trans hscaled hden
  contains_point_values := by
    intro I hI x hx n hxlo hxhi
    have hIlo : a <= I.lo := hI.1
    have hIhi : I.hi <= b := hI.2.2
    have hxlip := hlip.2 I.lo x hIlo (Rat.le_trans hI.2.1 hIhi)
      (Rat.le_trans hIlo hxlo) (Rat.le_trans hxhi hIhi)
    have hdiff : qabs (x - I.lo) = x - I.lo := by
      rw [qabs_eq_self_of_nonneg]
      grind [Rat.sub_eq_add_neg]
    have hwithin : x - I.lo <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hwithin
      (by exact_mod_cast Nat.zero_le L : (0 : Rat) <= (L : Rat))
    have hforward : f I.lo - f x <= (L : Rat) * (x - I.lo) := by
      calc
        f I.lo - f x <= qabs (f I.lo - f x) := self_le_qabs _
        _ <= (L : Rat) * (x - I.lo) := by simpa [hdiff] using hxlip
    have hreverse : f x - f I.lo <= (L : Rat) * (x - I.lo) := by
      calc
        f x - f I.lo = -(f I.lo - f x) := by
          grind [Rat.sub_eq_add_neg]
        _ <= qabs (f I.lo - f x) := by
          simpa [qabs_neg] using (self_le_qabs (-(f I.lo - f x)))
        _ <= (L : Rat) * (x - I.lo) := by simpa [hdiff] using hxlip
    have hlow : f I.lo - (L : Rat) * I.width <= f x := by
      grind [Rat.sub_eq_add_neg]
    have hupp : f x <= f I.lo + (L : Rat) * I.width := by
      grind [Rat.sub_eq_add_neg]
    change QInterval.ContainsInterval
      { lo := f I.lo - (L : Rat) * I.width,
        hi := f I.lo + (L : Rat) * I.width }
      { lo := f x, hi := f x }
    exact ⟨hlow, hupp⟩
/-- Turn a rational Lipschitz certificate on the unit chart into the
interval-image certificate consumed by the FTC layer. -/
def IntervalRegularOn.of_lipschitzOnUnit
    (f : Rat -> Rat) (L : Nat)
    (hlip : Integral.LipschitzOnUnit f (L : Rat)) :
    IntervalRegularOn (FunctionOnInterval.exactRat f 0 1) where
  evalInterval := fun I _I _n =>
    { lo := f I.lo - (L : Rat) * I.width
      hi := f I.lo + (L : Rat) * I.width }
  inputPrecision := fun n => (2 * L + 1) * (n + 1)
  inputPrecision_pos := by
    intro n
    exact Nat.mul_pos (by omega) (Nat.succ_pos n)
  output_width := by
    intro I hI n hsmall
    have hL0 : 0 <= (L : Rat) := by exact_mod_cast Nat.zero_le L
    have hwidth : 0 <= I.width := by
      unfold QInterval.width
      grind [hI.2.1]
    have hscaled :
        (2 * (L : Rat)) * I.width <=
          (2 * (L : Rat)) /
            (((2 * L + 1) * (n + 1) : Nat) : Rat) := by
      have hscaled0 := Rat.mul_le_mul_of_nonneg_left hsmall
        (Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ 2) hL0)
      simpa [Rat.div_def, Rat.mul_assoc] using hscaled0
    have hden :
        (2 * (L : Rat)) /
            (((2 * L + 1) * (n + 1) : Nat) : Rat) <=
          1 / (((n + 1 : Nat) : Rat)) := by
      have hnpos : 0 < ((n + 1 : Nat) : Rat) :=
        (Rat.natCast_pos).2 (Nat.succ_pos n)
      have hfactor : 0 < (((2 * L + 1) * (n + 1) : Nat) : Rat) := by
        exact_mod_cast (Nat.mul_pos (by omega) (Nat.succ_pos n))
      apply Rat.le_of_mul_le_mul_right
        (c := (((2 * L + 1) * (n + 1) : Nat) : Rat) *
          ((n + 1 : Nat) : Rat))
      · rw [Rat.div_def, Rat.div_def]
        rw [show (((2 * L + 1) * (n + 1) : Nat) : Rat) =
          (2 * (L : Rat) + 1) * ((n + 1 : Nat) : Rat) by
            rw [Rat.natCast_mul, Rat.natCast_add, Rat.natCast_mul,
              Rat.natCast_add]
            grind]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      · exact Rat.mul_pos hfactor hnpos
    constructor
    · change 0 <=
        (f I.lo + (L : Rat) * I.width) -
          (f I.lo - (L : Rat) * I.width)
      have hnonneg : 0 <= (2 * (L : Rat)) * I.width :=
        Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hL0) hwidth
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
    · change
        (f I.lo + (L : Rat) * I.width) -
            (f I.lo - (L : Rat) * I.width) <=
          1 / (((n + 1 : Nat) : Rat))
      have hwidth_eq :
          (f I.lo + (L : Rat) * I.width) -
              (f I.lo - (L : Rat) * I.width) =
            (2 * (L : Rat)) * I.width := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      rw [hwidth_eq]
      exact Rat.le_trans hscaled hden
  contains_point_values := by
    intro I hI x hx n hxlo hxhi
    have hIlo : 0 <= I.lo := hI.1
    have hIhi : I.hi <= 1 := hI.2.2
    have hxlip := hlip.2 I.lo x hIlo (Rat.le_trans hI.2.1 hIhi)
      (Rat.le_trans hIlo hxlo) (Rat.le_trans hxhi hIhi)
    have hdiff : qabs (x - I.lo) = x - I.lo := by
      rw [qabs_eq_self_of_nonneg]
      grind [Rat.sub_eq_add_neg]
    have hwithin : x - I.lo <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hwithin
      (by exact_mod_cast Nat.zero_le L : (0 : Rat) <= (L : Rat))
    have hforward : f I.lo - f x <= (L : Rat) * (x - I.lo) := by
      calc
        f I.lo - f x <= qabs (f I.lo - f x) := self_le_qabs _
        _ <= (L : Rat) * (x - I.lo) := by simpa [hdiff] using hxlip
    have hreverse : f x - f I.lo <= (L : Rat) * (x - I.lo) := by
      calc
        f x - f I.lo = -(f I.lo - f x) := by
          grind [Rat.sub_eq_add_neg]
        _ <= qabs (f I.lo - f x) := by
          simpa [qabs_neg] using (self_le_qabs (-(f I.lo - f x)))
        _ <= (L : Rat) * (x - I.lo) := by simpa [hdiff] using hxlip
    have hlow : f I.lo - (L : Rat) * I.width <= f x := by
      grind [Rat.sub_eq_add_neg]
    have hupp : f x <= f I.lo + (L : Rat) * I.width := by
      grind [Rat.sub_eq_add_neg]
    change QInterval.ContainsInterval
      { lo := f I.lo - (L : Rat) * I.width,
        hi := f I.lo + (L : Rat) * I.width }
      { lo := f x, hi := f x }
    exact ⟨hlow, hupp⟩
/-! A scheduled variant of interval regularity.

The native computation stage of a `FunctionOnInterval` is part of its raw
representation and need not be the best stage for an interval enclosure over
a whole cell.  This contract therefore exposes an explicit `evalPrecision`:
the interval evaluator and its point-value containment proof use the same
chosen stage, while the requested output index remains `n`.  It is the
representation-level interface for adaptive algorithms; it does not assert
that the schedule is monotone or that it changes the underlying abstract
function. -/
structure ScheduledIntervalRegularOn (F : FunctionOnInterval) where
  evalInterval : (I : QInterval) -> subintervalOf I F.lower F.upper -> Nat -> QInterval
  evalPrecision : Nat -> Nat
  inputPrecision : Nat -> Nat
  inputPrecision_pos : forall n, 0 < inputPrecision n
  output_width :
    forall I hI n,
      I.width <= (1 / ((inputPrecision n) : Rat)) ->
        0 <= (evalInterval I hI n).width /\
        (evalInterval I hI n).width <= 1 / ((n + 1 : Nat) : Rat)
  contains_point_values :
    forall I hI x hx n,
      I.lo <= x ->
      x <= I.hi ->
        QInterval.ContainsInterval
        (evalInterval I hI n)
        (F.compute x hx (evalPrecision n))

/-! The scheduled and ordinary contracts are intentionally not identified by
stage monotonicity alone: a requested-stage box may be wider than the
adaptive-stage box.  This adapter records the exact additional certificate
needed to expose the scheduled evaluator through `IntervalRegularOn`. -/

def ScheduledIntervalRegularOn.toIntervalRegularOn_of_requested_stage
    {F : FunctionOnInterval} (h : ScheduledIntervalRegularOn F)
    (requested_stage_contains :
      forall I hI x hx n,
        I.lo <= x ->
        x <= I.hi ->
          QInterval.ContainsInterval
            (h.evalInterval I hI n)
            (F.compute x hx n)) :
    IntervalRegularOn F where
  evalInterval := h.evalInterval
  inputPrecision := h.inputPrecision
  inputPrecision_pos := h.inputPrecision_pos
  output_width := h.output_width
  contains_point_values := requested_stage_contains

/-- The common non-adaptive specialization of the scheduled contract.

When the interval evaluator reads the same computation stage requested by the
ordinary contract, its existing point-containment field is already the
requested-stage certificate.  This is deliberately a separate adapter from
`toIntervalRegularOn_of_requested_stage`: adaptive evaluators still need an
explicit transport theorem for their requested stages. -/
def ScheduledIntervalRegularOn.toIntervalRegularOn_of_identity_schedule
    {F : FunctionOnInterval} (h : ScheduledIntervalRegularOn F)
    (hschedule : forall n, h.evalPrecision n = n) :
    IntervalRegularOn F :=
  h.toIntervalRegularOn_of_requested_stage (by
    intro I hI x hx n hIlo hIhi
    simpa [hschedule n] using
      h.contains_point_values I hI x hx n hIlo hIhi)

/-- Repackage an ordinary interval-regular evaluator as a scheduled evaluator
with the identity stage schedule.  This is the canonical bridge for existing
pointwise proofs when a downstream construction expects the explicit schedule
field. -/
def IntervalRegularOn.toScheduledIntervalRegularOn_identity
    {F : FunctionOnInterval} (h : IntervalRegularOn F) :
    ScheduledIntervalRegularOn F where
  evalInterval := h.evalInterval
  evalPrecision := fun n => n
  inputPrecision := h.inputPrecision
  inputPrecision_pos := h.inputPrecision_pos
  output_width := h.output_width
  contains_point_values := h.contains_point_values

/-! Build interval regularity directly from a proof-independent point
evaluator.  The public `IntervalRegularOn` contract remains unchanged; this
constructor only removes domain-proof noise from new special-function
certificates. -/
def IntervalRegularOn.ofStable
    (f : StablePartialRealFunRaw)
    (a b : Rat)
    (defined_on : forall x, inDomainInterval a b x -> f.definedAt x)
    (valid_on : forall x, f.definedAt x ->
      RealCompute.ValidCompute (f.compute x))
    (evalInterval : (I : QInterval) -> subintervalOf I a b -> Nat -> QInterval)
    (inputPrecision : Nat -> Nat)
    (inputPrecision_pos : forall n, 0 < inputPrecision n)
    (output_width : forall I hI n,
      I.width <= (1 / ((inputPrecision n) : Rat)) ->
        0 <= (evalInterval I hI n).width /\
        (evalInterval I hI n).width <= 1 / ((n + 1 : Nat) : Rat))
    (contains_point_values : forall I hI x (hx : f.definedAt x) n,
      I.lo <= x -> x <= I.hi ->
        QInterval.ContainsInterval (evalInterval I hI n) (f.compute x n)) :
    IntervalRegularOn
      (FunctionOnInterval.ofStable f a b defined_on valid_on) where
  evalInterval := evalInterval
  inputPrecision := inputPrecision
  inputPrecision_pos := inputPrecision_pos
  output_width := output_width
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    change QInterval.ContainsInterval (evalInterval I hI n) (f.compute x n)
    exact contains_point_values I hI x (defined_on x hx) n hIlo hIhi

def stableExactRatConstant (c : Rat) : StablePartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun _ _ => { lo := c, hi := c }
  rate := fun _ => .unknown

def stableExactRatConstant_intervalRegularOn (c a b : Rat) :
    IntervalRegularOn
      (FunctionOnInterval.ofStable (stableExactRatConstant c) a b
        (fun _ _ => trivial)
        (fun _ _ => RealCompute.ofRat_valid c)) :=
  IntervalRegularOn.ofStable
    (stableExactRatConstant c) a b
    (fun _ _ => trivial)
    (fun _ _ => RealCompute.ofRat_valid c)
    (fun _ _ _ => { lo := c, hi := c })
    (fun _ => 1)
    (by intro n; omega)
    (by
      intro I hI n hsmall
      simp only [QInterval.width, Rat.sub_self]
      constructor
      · exact Rat.le_refl
      · exact Rat.le_of_lt (one_div_nat_pos (by omega)))
    (by
      intro I hI x hx n hIlo hIhi
      exact ⟨Rat.le_refl, Rat.le_refl⟩)

/-- Exact constant functions satisfy the interval-regularity contract with a
point-valued evaluator.  This is the first concrete bridge from the
pointwise interval-function layer to the effective continuity/Riemann layer;
no limit or completed-real argument is involved. -/
def exactRat_constant_intervalRegularOn (c a b : Rat) :
    IntervalRegularOn (FunctionOnInterval.exactRat (fun _ => c) a b) where
  evalInterval := fun _I _hI _n => { lo := c, hi := c }
  inputPrecision := fun _n => 1
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    simp only [QInterval.width, Rat.sub_self]
    constructor
    · exact Rat.le_refl
    · exact Rat.le_of_lt (one_div_nat_pos (by omega))
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    change QInterval.ContainsInterval
      { lo := c, hi := c } { lo := c, hi := c }
    exact ⟨Rat.le_refl, Rat.le_refl⟩

/-- The same exact constant evaluator also satisfies the explicit modulus
presentation used by effective continuity consumers. -/
def exactRat_constant_effectiveModulusFor (c a b : Rat) :
    EffectiveModulusFor (FunctionOnInterval.exactRat (fun _ => c) a b) where
  inputPrecision := fun _n => 1
  evalPrecision := fun _n => 0
  close := by
    intro x y n hx hy hxy
    by_cases hn : n = 0
    · change QInterval.NearAt { lo := c, hi := c } { lo := c, hi := c }
        (precisionAtStage n)
      unfold QInterval.NearAt QInterval.width
      simp [precisionAtStage, hn] <;> grind [Rat.sub_eq_add_neg]
    · have hnonneg : 0 <= (1 / (n : Rat)) :=
        Rat.le_of_lt (one_div_nat_pos (Nat.pos_of_ne_zero hn))
      change QInterval.NearAt { lo := c, hi := c } { lo := c, hi := c }
        (precisionAtStage n)
      unfold QInterval.NearAt QInterval.width
      simp [precisionAtStage, hn, hnonneg] <;> grind [Rat.sub_eq_add_neg]

/-- An interval-regular evaluator supplies literal rational
epsilon-delta continuity.  The output target at stage `n` is `1/(n+1)`, so
stage zero is meaningful for non-exact interval algorithms.  The proof uses
the finite denominator-derived stage `eps.den`, encloses both point evaluations
in one narrow image interval, and never invokes topology or a completed real
line. -/
theorem IntervalRegularOn.epsilonDeltaContinuous
    {F : FunctionOnInterval} (h : IntervalRegularOn F) :
    EpsilonDeltaContinuousOn F := by
  intro eps
  let n : Nat := eps.val.den
  let delta : QPos :=
    { val := 1 / ((h.inputPrecision n : Nat) : Rat)
      property := one_div_nat_pos (h.inputPrecision_pos n) }
  refine ⟨delta, n, ?_⟩
  intro x y hx hy hxy
  let I : QInterval := { lo := min x y, hi := max x y }
  have hI : subintervalOf I F.lower F.upper := by
    rcases hx with ⟨hxlo, hxhi⟩
    rcases hy with ⟨hylo, hyhi⟩
    dsimp [I]
    constructor
    · grind
    constructor <;> grind
  have hIwidth : I.width = qabs (y - x) := by
    dsimp [I]
    exact QInterval.endpointHull_width x y
  have hsmall : I.width <= 1 / ((h.inputPrecision n : Nat) : Rat) := by
    rw [hIwidth]
    simpa [delta] using hxy
  have houtput := h.output_width I hI n hsmall
  have htarget : 1 / (((n + 1 : Nat) : Rat)) <= eps.val := by
    dsimp [n]
    exact one_div_den_succ_le_of_pos eps.property
  have hYwidth : (h.evalInterval I hI n).width <= eps.val :=
    Rat.le_trans houtput.2 htarget
  have hxlo : I.lo <= x := by
    dsimp [I]
    grind
  have hxhi : x <= I.hi := by
    dsimp [I]
    grind
  have hylo : I.lo <= y := by
    dsimp [I]
    grind
  have hyhi : y <= I.hi := by
    dsimp [I]
    grind
  have hcontainsX := h.contains_point_values I hI x hx n hxlo hxhi
  have hcontainsY := h.contains_point_values I hI y hy n hylo hyhi
  have hXwidth_nonneg := (F.valid_on x (F.defined_on x hx)).1 n
  have hYwidth_nonneg := (F.valid_on y (F.defined_on y hy)).1 n
  have hXordered : (F.compute x hx n).lo <= (F.compute x hx n).hi := by
    change 0 <= (F.compute x hx n).hi - (F.compute x hx n).lo at hXwidth_nonneg
    grind [Rat.sub_eq_add_neg]
  have hYordered : (F.compute y hy n).lo <= (F.compute y hy n).hi := by
    change 0 <= (F.compute y hy n).hi - (F.compute y hy n).lo at hYwidth_nonneg
    grind [Rat.sub_eq_add_neg]
  have hwidthX : (F.compute x hx n).width <= eps.val :=
    Rat.le_trans (QInterval.width_le_of_contains hcontainsX) hYwidth
  have hwidthY : (F.compute y hy n).width <= eps.val :=
    Rat.le_trans (QInterval.width_le_of_contains hcontainsY) hYwidth
  unfold QInterval.NearAt
  constructor
  · change (F.compute x hx n).lo <= (F.compute y hy n).hi + eps.val
    unfold QInterval.ContainsInterval at hcontainsX hcontainsY
    unfold QInterval.width at hYwidth
    grind [Rat.sub_eq_add_neg]
  constructor
  · change (F.compute y hy n).lo <= (F.compute x hx n).hi + eps.val
    unfold QInterval.ContainsInterval at hcontainsX hcontainsY
    unfold QInterval.width at hYwidth
    grind [Rat.sub_eq_add_neg]
  exact ⟨hwidthX, hwidthY⟩

/-- Scheduled interval regularity also gives rational epsilon-delta
continuity.  The only additional bookkeeping is that both point boxes are
read at the certificate's explicit `evalPrecision n`; no limit object or
completed real line is introduced. -/
theorem ScheduledIntervalRegularOn.epsilonDeltaContinuous
    {F : FunctionOnInterval} (h : ScheduledIntervalRegularOn F) :
    EpsilonDeltaContinuousOn F := by
  intro eps
  let n : Nat := eps.val.den
  let delta : QPos :=
    { val := 1 / ((h.inputPrecision n : Nat) : Rat)
      property := one_div_nat_pos (h.inputPrecision_pos n) }
  refine ⟨delta, h.evalPrecision n, ?_⟩
  intro x y hx hy hxy
  let I : QInterval := { lo := min x y, hi := max x y }
  have hI : subintervalOf I F.lower F.upper := by
    rcases hx with ⟨hxlo, hxhi⟩
    rcases hy with ⟨hylo, hyhi⟩
    dsimp [I]
    constructor
    · grind
    constructor <;> grind
  have hIwidth : I.width = qabs (y - x) := by
    dsimp [I]
    exact QInterval.endpointHull_width x y
  have hsmall : I.width <= 1 / ((h.inputPrecision n : Nat) : Rat) := by
    rw [hIwidth]
    simpa [delta] using hxy
  have houtput := h.output_width I hI n hsmall
  have htarget : 1 / (((n + 1 : Nat) : Rat)) <= eps.val := by
    dsimp [n]
    exact one_div_den_succ_le_of_pos eps.property
  have hYwidth : (h.evalInterval I hI n).width <= eps.val :=
    Rat.le_trans houtput.2 htarget
  have hxlo : I.lo <= x := by
    dsimp [I]
    grind
  have hxhi : x <= I.hi := by
    dsimp [I]
    grind
  have hylo : I.lo <= y := by
    dsimp [I]
    grind
  have hyhi : y <= I.hi := by
    dsimp [I]
    grind
  let p : Nat := h.evalPrecision n
  have hcontainsX := h.contains_point_values I hI x hx n hxlo hxhi
  have hcontainsY := h.contains_point_values I hI y hy n hylo hyhi
  have hXwidth_nonneg := (F.valid_on x (F.defined_on x hx)).1 p
  have hYwidth_nonneg := (F.valid_on y (F.defined_on y hy)).1 p
  have hXordered : (F.compute x hx p).lo <= (F.compute x hx p).hi := by
    change 0 <= (F.compute x hx p).hi - (F.compute x hx p).lo at hXwidth_nonneg
    grind [Rat.sub_eq_add_neg]
  have hYordered : (F.compute y hy p).lo <= (F.compute y hy p).hi := by
    change 0 <= (F.compute y hy p).hi - (F.compute y hy p).lo at hYwidth_nonneg
    grind [Rat.sub_eq_add_neg]
  have hwidthX : (F.compute x hx p).width <= eps.val :=
    Rat.le_trans (QInterval.width_le_of_contains hcontainsX) hYwidth
  have hwidthY : (F.compute y hy p).width <= eps.val :=
    Rat.le_trans (QInterval.width_le_of_contains hcontainsY) hYwidth
  unfold QInterval.NearAt
  constructor
  · change (F.compute x hx p).lo <= (F.compute y hy p).hi + eps.val
    unfold QInterval.ContainsInterval at hcontainsX hcontainsY
    unfold QInterval.width at hYwidth
    grind [Rat.sub_eq_add_neg]
  constructor
  · change (F.compute y hy p).lo <= (F.compute x hx p).hi + eps.val
    unfold QInterval.ContainsInterval at hcontainsX hcontainsY
    unfold QInterval.width at hYwidth
    grind [Rat.sub_eq_add_neg]
  exact ⟨hwidthX, hwidthY⟩

/-- A certified continuous function on a rational interval.

This is the theorem-facing package.  `FunctionOnInterval` says the evaluator is
available at rational points on the interval; `regular` is the interval-level
continuity data that lets us choose subdivisions and evaluation precision. -/
structure ContinuousFunctionOnInterval where
  function : FunctionOnInterval
  regular : IntervalRegularOn function

/-- Constructive monotonicity on rational points of the interval.

The field `increasing` means nondecreasing; its negation selects the
nonincreasing case.  This is order data, not yet enough to build an inverse
algorithm by itself. -/
structure MonotoneOnInterval (F : FunctionOnInterval) where
  increasing : Prop
  monotone_inc :
    increasing ->
      forall x y
        (hx : inDomainInterval F.lower F.upper x)
        (hy : inDomainInterval F.lower F.upper y),
        x <= y ->
          forall n,
            (F.compute x hx n).lo <= (F.compute y hy n).hi
  monotone_dec :
    ¬ increasing ->
      forall x y
        (hx : inDomainInterval F.lower F.upper x)
        (hy : inDomainInterval F.lower F.upper y),
        x <= y ->
          forall n,
            (F.compute y hy n).lo <= (F.compute x hx n).hi

/-- Nondecreasing means increasing in the weak order sense used by the
project: rational inputs with `x <= y` have compatible output intervals with
the value at `x` no larger than the value at `y`. -/
def NondecreasingOnInterval (F : FunctionOnInterval) : Prop :=
  forall x y
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y),
    x <= y ->
      forall n,
        (F.compute x hx n).lo <= (F.compute y hy n).hi

/-- Nonincreasing is the reversed weak interval order. -/
def NonincreasingOnInterval (F : FunctionOnInterval) : Prop :=
  forall x y
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y),
    x <= y ->
      forall n,
        (F.compute y hy n).lo <= (F.compute x hx n).hi

namespace MonotoneOnInterval

def ofNondecreasing {F : FunctionOnInterval}
    (h : NondecreasingOnInterval F) :
    MonotoneOnInterval F where
  increasing := True
  monotone_inc := by
    intro _hinc
    exact h
  monotone_dec := by
    intro hfalse
    exact False.elim (hfalse trivial)

def ofNonincreasing {F : FunctionOnInterval}
    (h : NonincreasingOnInterval F) :
    MonotoneOnInterval F where
  increasing := False
  monotone_inc := by
    intro hfalse
    cases hfalse
  monotone_dec := by
    intro _hdec
    exact h

theorem nondecreasing {F : FunctionOnInterval}
    (h : MonotoneOnInterval F) (hinc : h.increasing) :
    NondecreasingOnInterval F :=
  h.monotone_inc hinc

theorem nonincreasing {F : FunctionOnInterval}
    (h : MonotoneOnInterval F) (hdec : ¬ h.increasing) :
    NonincreasingOnInterval F :=
  h.monotone_dec hdec

def restrict {F : FunctionOnInterval}
    (h : MonotoneOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    MonotoneOnInterval (F.restrict a b hlo hab hhi) where
  increasing := h.increasing
  monotone_inc := by
    intro hinc x y hx hy hxy n
    exact h.monotone_inc hinc x y
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
      ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
      hxy n
  monotone_dec := by
    intro hdec x y hx hy hxy n
    exact h.monotone_dec hdec x y
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
      ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
      hxy n

end MonotoneOnInterval

namespace NondecreasingOnInterval

theorem restrict {F : FunctionOnInterval}
    (h : NondecreasingOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    NondecreasingOnInterval (F.restrict a b hlo _hab hhi) := by
  intro x y hx hy hxy n
  exact h x y
    ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
    ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
    hxy n

end NondecreasingOnInterval

namespace NonincreasingOnInterval

theorem restrict {F : FunctionOnInterval}
    (h : NonincreasingOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    NonincreasingOnInterval (F.restrict a b hlo _hab hhi) := by
  intro x y hx hy hxy n
  exact h x y
    ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
    ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
    hxy n

end NonincreasingOnInterval

namespace Integral

/-- The finite endpoint range used by a nondecreasing Darboux cell.

For a rational cell `[p,r]`, the lower endpoint is evaluated at `p` and the
upper endpoint at `r`, both at one explicitly supplied finite evaluator
stage.  This is only the cell computation; interval regularity and a width
argument remain responsible for turning its partition sums into a valid raw
real. -/
def nondecreasingDarbouxRange (F : FunctionOnInterval)
    (P : RationalPartition F.lower F.upper)
    (k : Nat) (hk : k < P.pieces) (prec : Nat) : QInterval :=
  let C := P.cell k hk
  { lo := (F.compute C.lower
      (And.intro C.lower_mem (Rat.le_trans C.ordered C.upper_mem)) prec).lo
    hi := (F.compute C.upper
      (And.intro (Rat.le_trans C.lower_mem C.ordered) C.upper_mem) prec).hi }

/-- Weak nondecreasingness is exactly enough to order each finite endpoint
range.  No value on an unrepresented completed interval is used here. -/
theorem nondecreasingDarbouxRange_width_nonneg
    (F : FunctionOnInterval) (hF : NondecreasingOnInterval F)
    (P : RationalPartition F.lower F.upper)
    (k : Nat) (hk : k < P.pieces) (prec : Nat) :
    0 <= (nondecreasingDarbouxRange F P k hk prec).width := by
  let C := P.cell k hk
  have hlower : inDomainInterval F.lower F.upper C.lower :=
    And.intro C.lower_mem (Rat.le_trans C.ordered C.upper_mem)
  have hupper : inDomainInterval F.lower F.upper C.upper :=
    And.intro (Rat.le_trans C.lower_mem C.ordered) C.upper_mem
  have horder := hF C.lower C.upper hlower hupper C.ordered prec
  change 0 <= (F.compute C.upper hupper prec).hi -
    (F.compute C.lower hlower prec).lo
  grind [Rat.sub_eq_add_neg]

/-! Interval regularity supplies a common image box for both endpoints of a
cell.  Consequently the endpoint range used by the finite Darboux sum has
the same output-width budget. -/
theorem nondecreasingDarbouxRange_width_le_of_intervalRegular
    (F : FunctionOnInterval)
    (hregular : IntervalRegularOn F)
    (P : RationalPartition F.lower F.upper)
    (k : Nat) (hk : k < P.pieces) (prec : Nat)
    (hsmall : (P.cell k hk).width <=
      1 / ((hregular.inputPrecision prec : Nat) : Rat)) :
    (nondecreasingDarbouxRange F P k hk prec).width <=
      1 / ((prec + 1 : Nat) : Rat) := by
  let C := P.cell k hk
  have hlower : inDomainInterval F.lower F.upper C.lower :=
    And.intro C.lower_mem (Rat.le_trans C.ordered C.upper_mem)
  have hupper : inDomainInterval F.lower F.upper C.upper :=
    And.intro (Rat.le_trans C.lower_mem C.ordered) C.upper_mem
  let I : QInterval := { lo := C.lower, hi := C.upper }
  have hI : subintervalOf I F.lower F.upper := by
    exact ⟨C.lower_mem, C.ordered, C.upper_mem⟩
  have houtput := hregular.output_width I hI prec (by
    change C.width <= _
    exact hsmall)
  have hleft := hregular.contains_point_values I hI C.lower hlower prec
    (by simp [I]) (by simpa [I] using C.ordered)
  have hright := hregular.contains_point_values I hI C.upper hupper prec
    (by simpa [I] using C.ordered) (by simp [I])
  change (F.compute C.upper hupper prec).hi -
    (F.compute C.lower hlower prec).lo <= 1 / ((prec + 1 : Nat) : Rat)
  have himage :
      (hregular.evalInterval I hI prec).width <=
        1 / ((prec + 1 : Nat) : Rat) := houtput.2
  have hlower_bound :
      (hregular.evalInterval I hI prec).lo <=
        (F.compute C.lower hlower prec).lo :=
    hleft.1
  have hupper_bound :
      (F.compute C.upper hupper prec).hi <=
        (hregular.evalInterval I hI prec).hi :=
    hright.2
  grind [QInterval.width, Rat.sub_eq_add_neg]

theorem nondecreasingDarbouxStage_width_nonneg
    (F : FunctionOnInterval) (hF : NondecreasingOnInterval F)
    (P : RationalPartition F.lower F.upper) (prec : Nat) :
    0 <= (P.boundIntegralSum
      (fun k hk => nondecreasingDarbouxRange F P k hk prec)).width := by
  unfold RationalPartition.boundIntegralSum
  rw [RationalPartition.addInterval_fold_width]
  have hterm : forall k, k ∈ List.range P.pieces ->
      0 <= (P.boundIntegralTerm
        (fun j hj => nondecreasingDarbouxRange F P j hj prec) k).width := by
    intro k hk
    have hklt : k < P.pieces := List.mem_range.mp hk
    simp only [RationalPartition.boundIntegralTerm, dif_pos hklt]
    rw [RationalSubinterval.scaleBound,
      QInterval.scaleByRat_width_of_nonneg]
    · exact Rat.mul_nonneg (by
        unfold RationalSubinterval.width
        have hcell := (P.cell k hklt).ordered
        grind)
        (nondecreasingDarbouxRange_width_nonneg F hF P k hklt prec)
    · unfold RationalSubinterval.width
      have hcell := (P.cell k hklt).ordered
      grind
  have fold_nonneg : forall xs : List Nat, forall initial : Rat,
      (forall k, k ∈ xs ->
        0 <= (P.boundIntegralTerm
          (fun j hj => nondecreasingDarbouxRange F P j hj prec) k).width) ->
      0 <= initial ->
      0 <= xs.foldl (fun total k => total +
        (P.boundIntegralTerm
          (fun j hj => nondecreasingDarbouxRange F P j hj prec) k).width) initial := by
    intro xs initial
    induction xs generalizing initial with
    | nil =>
      intro _hterms hinit
      simpa using hinit
    | cons k xs ih =>
      intro hterms hinit
      have hk := hterms k (by simp)
      have hrest := ih (initial +
        (P.boundIntegralTerm
          (fun j hj => nondecreasingDarbouxRange F P j hj prec) k).width)
        (fun j hj => hterms j (by simp [hj]))
        (Rat.add_nonneg hinit hk)
      exact hrest
  have hsum := fold_nonneg (List.range P.pieces) 0 hterm (by decide +kernel)
  have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
    unfold QInterval.width
    grind
  rw [hzero]
  change 0 <= 0 + (List.range P.pieces).foldl
    (fun total k => total +
      (P.boundIntegralTerm
        (fun j hj => nondecreasingDarbouxRange F P j hj prec) k).width) 0
  simpa only [Rat.zero_add] using hsum

/-- The exact finite lower/upper Darboux bracket on a supplied rational
partition.  Its `k`th summand is the cell width times the endpoint range.
This direct finite calculation is intentionally exposed before a general
validity theorem is available. -/
def nondecreasingDarbouxStage (F : FunctionOnInterval)
    (P : RationalPartition F.lower F.upper) (prec : Nat) : QInterval :=
  P.boundIntegralSum
    (fun k hk => nondecreasingDarbouxRange F P k hk prec)

theorem exactRat_nondecreasingDarbouxStage_stage_independent
    (f : Rat -> Rat) (a b : Rat) (P : RationalPartition a b) (n m : Nat) :
    nondecreasingDarbouxStage
      (FunctionOnInterval.exactRat f a b) P n =
      nondecreasingDarbouxStage
        (FunctionOnInterval.exactRat f a b) P m := by
  rfl

/-- The static dyadic instance of `nondecreasingDarbouxStage` used by the
chapter's increasing-function pseudocode.  The nondecreasing proof is not an
input to this executable calculation; it is consumed by the later orderedness
and shrinking certificates. -/
def nondecreasingDarbouxDyadicStage (F : FunctionOnInterval)
    (hinterval : F.lower <= F.upper) (evalPrecision : Nat -> Nat)
    (n : Nat) : QInterval :=
  let P := RationalPartition.uniform F.lower F.upper (2 ^ n)
    (Nat.pow_pos (by omega : 0 < 2)) hinterval
  nondecreasingDarbouxStage F P (evalPrecision n)

/-! The cell estimate composes with the finite uniform-partition fold. -/
theorem nondecreasingDarbouxStage_width_le_of_uniform_input_budget
    (F : FunctionOnInterval) (hregular : IntervalRegularOn F)
    (pieces : Nat) (hpieces : 0 < pieces) (hab : F.lower <= F.upper)
    (prec : Nat)
    (hsmall : mesh F.lower F.upper pieces <=
      1 / ((hregular.inputPrecision prec : Nat) : Rat)) :
    (nondecreasingDarbouxStage F
      (RationalPartition.uniform F.lower F.upper pieces hpieces hab) prec).width <=
      (F.upper - F.lower) * (1 / ((prec + 1 : Nat) : Rat)) := by
  unfold nondecreasingDarbouxStage
  apply RationalPartition.uniform_boundIntegralSum_width_le
    pieces hpieces hab
    (fun k hk => nondecreasingDarbouxRange F
      (RationalPartition.uniform F.lower F.upper pieces hpieces hab) k hk prec)
    (1 / ((prec + 1 : Nat) : Rat))
  intro k hk
  apply nondecreasingDarbouxRange_width_le_of_intervalRegular
    F hregular (RationalPartition.uniform F.lower F.upper pieces hpieces hab) k hk prec
  simpa [RationalPartition.uniform_cell_width F.lower F.upper pieces hpieces hab k hk]
    using hsmall

theorem nondecreasingDarbouxStage_width_le_of_uniform_input_budget_and_tolerance
    (F : FunctionOnInterval) (hregular : IntervalRegularOn F)
    (pieces : Nat) (hpieces : 0 < pieces) (hab : F.lower <= F.upper)
    (prec : Nat)
    (hsmall : mesh F.lower F.upper pieces <=
      1 / ((hregular.inputPrecision prec : Nat) : Rat))
    (eps : Rat)
    (hbudget : (F.upper - F.lower) *
        (1 / ((prec + 1 : Nat) : Rat)) <= eps) :
    (nondecreasingDarbouxStage F
      (RationalPartition.uniform F.lower F.upper pieces hpieces hab) prec).width <=
      eps := by
  exact Rat.le_trans
    (nondecreasingDarbouxStage_width_le_of_uniform_input_budget
      F hregular pieces hpieces hab prec hsmall)
    hbudget

/-! The dyadic presentation is just the uniform certificate at pieces `2^n`.
The input-budget premise remains explicit: dyadic mesh refinement alone does
not justify a completed integral when the evaluator's input schedule is
unspecified. -/
theorem nondecreasingDarbouxDyadicStage_width_le_of_input_budget
    (F : FunctionOnInterval) (hregular : IntervalRegularOn F)
    (hinterval : F.lower <= F.upper) (evalPrecision : Nat -> Nat) (n : Nat)
    (hsmall : mesh F.lower F.upper (2 ^ n) <=
      1 / ((hregular.inputPrecision (evalPrecision n) : Nat) : Rat)) :
    (nondecreasingDarbouxDyadicStage F hinterval evalPrecision n).width <=
      (F.upper - F.lower) *
        (1 / ((evalPrecision n + 1 : Nat) : Rat)) := by
  unfold nondecreasingDarbouxDyadicStage
  apply nondecreasingDarbouxStage_width_le_of_uniform_input_budget
    F hregular (2 ^ n) (Nat.pow_pos (by omega : 0 < 2)) hinterval
    (evalPrecision n)
  exact hsmall

theorem nondecreasingDarbouxDyadicStage_width_le_of_input_budget_and_tolerance
    (F : FunctionOnInterval) (hregular : IntervalRegularOn F)
    (hinterval : F.lower <= F.upper) (evalPrecision : Nat -> Nat) (n : Nat)
    (hsmall : mesh F.lower F.upper (2 ^ n) <=
      1 / ((hregular.inputPrecision (evalPrecision n) : Nat) : Rat))
    (eps : Rat)
    (hbudget : (F.upper - F.lower) *
        (1 / ((evalPrecision n + 1 : Nat) : Rat)) <= eps) :
    (nondecreasingDarbouxDyadicStage F hinterval evalPrecision n).width <=
      eps := by
  exact Rat.le_trans
    (nondecreasingDarbouxDyadicStage_width_le_of_input_budget
      F hregular hinterval evalPrecision n hsmall)
    hbudget

/-! A schedule-level bridge for the monotone Darboux algorithm.  The
finite width theorem above is useful only once its stages are assembled into
a valid raw computation.  This structure records precisely the remaining
finite data: the mesh/input-precision budget, stage nesting, and the
potential-infinity width witness.  No completed integral or completeness
principle is hidden in the package. -/

def monotoneDarbouxScheduleCompute
    (F : FunctionOnInterval) (hinterval : F.lower <= F.upper)
    (pieces evalPrecision : Nat -> Nat)
    (hpieces : forall n, 0 < pieces n) (n : Nat) : QInterval :=
  nondecreasingDarbouxStage F
    (RationalPartition.uniform F.lower F.upper (pieces n)
      (hpieces n) hinterval)
    (evalPrecision n)

structure MonotoneDarbouxSchedule
    (F : FunctionOnInterval) (hregular : IntervalRegularOn F)
    (hmonotone : NondecreasingOnInterval F)
    (hinterval : F.lower <= F.upper) where
  pieces : Nat -> Nat
  evalPrecision : Nat -> Nat
  pieces_pos : forall n, 0 < pieces n
  input_budget : forall n,
    mesh F.lower F.upper (pieces n) <=
      1 / ((hregular.inputPrecision (evalPrecision n) : Nat) : Rat)
  nested : forall n m, n <= m ->
    (monotoneDarbouxScheduleCompute F hinterval pieces evalPrecision
      pieces_pos n).lo <=
      (monotoneDarbouxScheduleCompute F hinterval pieces evalPrecision
        pieces_pos m).lo /\
    (monotoneDarbouxScheduleCompute F hinterval pieces evalPrecision
      pieces_pos m).hi <=
      (monotoneDarbouxScheduleCompute F hinterval pieces evalPrecision
        pieces_pos n).hi
  widths_shrink : RealCompute.WidthsShrinkToZero
    (monotoneDarbouxScheduleCompute F hinterval pieces evalPrecision
      pieces_pos)

def monotoneDarbouxScheduleRaw
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (s : MonotoneDarbouxSchedule F hregular hmonotone hinterval) : RealCompute :=
  { compute := monotoneDarbouxScheduleCompute F hinterval s.pieces
      s.evalPrecision s.pieces_pos
    rate := .unknown }

theorem monotoneDarbouxScheduleRaw_valid
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (s : MonotoneDarbouxSchedule F hregular hmonotone hinterval) :
    (monotoneDarbouxScheduleRaw s).Valid := by
  have hwidth : forall n,
      0 <= (monotoneDarbouxScheduleCompute F hinterval s.pieces
        s.evalPrecision s.pieces_pos n).width := by
    intro n
    change 0 <=
      ((RationalPartition.uniform F.lower F.upper (s.pieces n)
        (s.pieces_pos n) hinterval).boundIntegralSum
        (fun k hk => nondecreasingDarbouxRange F
          (RationalPartition.uniform F.lower F.upper (s.pieces n)
            (s.pieces_pos n) hinterval) k hk (s.evalPrecision n))).width
    exact nondecreasingDarbouxStage_width_nonneg F hmonotone _ _
  change RealCompute.ValidCompute
    (monotoneDarbouxScheduleCompute F hinterval s.pieces
      s.evalPrecision s.pieces_pos)
  refine ⟨hwidth, ?_, s.widths_shrink⟩
  intro n m hnm
  rcases s.nested n m hnm with ⟨hlo, hhi⟩
  refine ⟨hlo, ?_⟩
  constructor
  · have hm := hwidth m
    change 0 <=
      (monotoneDarbouxScheduleCompute F hinterval s.pieces
        s.evalPrecision s.pieces_pos m).hi -
      (monotoneDarbouxScheduleCompute F hinterval s.pieces
        s.evalPrecision s.pieces_pos m).lo at hm
    grind [Rat.sub_eq_add_neg]
  · exact hhi

theorem monotoneDarbouxScheduleRaw_width_le_of_tolerance
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (s : MonotoneDarbouxSchedule F hregular hmonotone hinterval)
    (n : Nat) (eps : Rat)
    (hbudget : (F.upper - F.lower) *
        (1 / ((s.evalPrecision n + 1 : Nat) : Rat)) <= eps) :
    ((monotoneDarbouxScheduleRaw s).compute n).width <= eps := by
  change (monotoneDarbouxScheduleCompute F hinterval s.pieces
    s.evalPrecision s.pieces_pos n).width <= eps
  exact Rat.le_trans
    (nondecreasingDarbouxStage_width_le_of_uniform_input_budget
      F hregular (s.pieces n) (s.pieces_pos n) hinterval
      (s.evalPrecision n) (s.input_budget n))
    hbudget

/-- Convert a certified monotone Darboux schedule into the public integral
construction interface.  The executable computation is exactly the schedule's
equal-mesh endpoint sum; the schedule validity theorem supplies the
`RealCompute.ValidCompute` certificate required by `CandidateConstructionFor`. -/
def monotoneDarbouxScheduleCandidateConstructionFor
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (s : MonotoneDarbouxSchedule F hregular hmonotone hinterval) :
    Integral.CandidateConstructionFor F where
  compute := (monotoneDarbouxScheduleRaw s).compute
  certificate := monotoneDarbouxScheduleRaw_valid s

theorem monotoneDarbouxScheduleCandidateConstructionFor_compute
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (s : MonotoneDarbouxSchedule F hregular hmonotone hinterval) :
    (monotoneDarbouxScheduleCandidateConstructionFor s).compute =
      monotoneDarbouxScheduleCompute F hinterval s.pieces
        s.evalPrecision s.pieces_pos := rfl

def monotoneDarbouxScheduleCandidateValueFor
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (s : MonotoneDarbouxSchedule F hregular hmonotone hinterval) : RealCompute :=
  Integral.candidateValueFor F (monotoneDarbouxScheduleCandidateConstructionFor s)

theorem monotoneDarbouxScheduleCandidateValueFor_valid
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (s : MonotoneDarbouxSchedule F hregular hmonotone hinterval) :
    (monotoneDarbouxScheduleCandidateValueFor s).Valid :=
  Integral.candidateValueFor_valid F (monotoneDarbouxScheduleCandidateConstructionFor s)

/-- A computation candidate accompanied by monotonicity of the integrand.

The intended construction is by lower and upper endpoint sums on a static
dyadic mesh, with width controlled by total variation times mesh size.  The
present structure separates that monotonicity certificate from the resulting
valid `CandidateConstructionFor`. Monotonicity and numerical validity alone do
not identify the candidate as an integral; use `Integral.HasIntegral` for that
claim and for mathematical laws about supplied integrals. -/
structure MonotoneCandidateConstructionFor (F : FunctionOnInterval) where
  monotone : MonotoneOnInterval F
  construction : CandidateConstructionFor F

theorem exactRat_constant_nondecreasing (c a b : Rat) :
    NondecreasingOnInterval
      (FunctionOnInterval.exactRat (fun _ => c) a b) := by
  intro x y hx hy hxy n
  change c <= c
  exact Rat.le_refl

/-! The first fully instantiated Darboux schedule.  The constant function on
the unit interval is deliberately small: every finite endpoint range is the
singleton `[1,1]`, so nesting is immediate while the construction still
passes through the public equal-mesh endpoint-sum algorithm. -/

def unitConstantMonotoneDarbouxSchedule :
    MonotoneDarbouxSchedule
      (FunctionOnInterval.exactRat (fun _ => (1 : Rat)) 0 1)
      (exactRat_constant_intervalRegularOn 1 0 1)
      (exactRat_constant_nondecreasing 1 0 1)
      (by decide +kernel) where
  pieces := fun _ => 1
  evalPrecision := fun _ => 0
  pieces_pos := by
    intro n
    decide +kernel
  input_budget := by
    intro n
    decide +kernel
  nested := by
    intro n m hnm
    simp [monotoneDarbouxScheduleCompute, nondecreasingDarbouxStage,
      nondecreasingDarbouxRange, FunctionOnInterval.exactRat,
      RationalPartition.uniform, RationalPartition.boundIntegralSum,
      RationalPartition.boundIntegralTerm, RationalSubinterval.scaleBound,
      QInterval.scaleByRat, RationalPartition.cell, RationalSubinterval.width,
      QInterval.width, QInterval.addInterval, leftPoint, mesh]
  widths_shrink := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    have hcell : (0 : Rat) ≤
        0 + (0 + 1) * ((1 - 0) / 1) - (0 + 0) := by
      decide +kernel
    have hwidth :
        (monotoneDarbouxScheduleCompute
          (FunctionOnInterval.exactRat (fun _ => (1 : Rat)) 0 1)
          (by decide +kernel)
          (fun _ => 1) (fun _ => 0)
          (by intro k; decide +kernel) n).width = 0 := by
      simp [monotoneDarbouxScheduleCompute, nondecreasingDarbouxStage,
        nondecreasingDarbouxRange, FunctionOnInterval.exactRat,
        RationalPartition.uniform, RationalPartition.boundIntegralSum,
        RationalPartition.boundIntegralTerm, RationalSubinterval.scaleBound,
        QInterval.scaleByRat, RationalPartition.cell, RationalSubinterval.width,
        QInterval.width, QInterval.addInterval, leftPoint, mesh, hcell,
        FunctionOnInterval.compute]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]
    rw [hwidth]
    exact Rat.le_of_lt eps.property

theorem unitConstantMonotoneDarbouxSchedule_integral_eq_one :
    (monotoneDarbouxScheduleCandidateValueFor
      unitConstantMonotoneDarbouxSchedule).Equiv (RealCompute.ofRat 1) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (monotoneDarbouxScheduleCandidateValueFor unitConstantMonotoneDarbouxSchedule)
    (RealCompute.ofRat 1) n n).2
  have hcell : (0 : Rat) ≤
      0 + (0 + 1) * ((1 - 0) / 1) - (0 + 0) := by
    decide +kernel
  have hcompute :
      (monotoneDarbouxScheduleCompute
        (FunctionOnInterval.exactRat (fun _ => (1 : Rat)) 0 1)
        (by decide +kernel)
        (fun _ => 1) (fun _ => 0)
        (by intro k; decide +kernel) n) = { lo := 1, hi := 1 } := by
    simp [monotoneDarbouxScheduleCompute, nondecreasingDarbouxStage,
      nondecreasingDarbouxRange, FunctionOnInterval.exactRat,
      RationalPartition.uniform, RationalPartition.boundIntegralSum,
      RationalPartition.boundIntegralTerm, RationalSubinterval.scaleBound,
      QInterval.scaleByRat, RationalPartition.cell, RationalSubinterval.width,
      QInterval.width, QInterval.addInterval, leftPoint, mesh, hcell,
      FunctionOnInterval.compute]
    grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  change QInterval.Overlaps
    (monotoneDarbouxScheduleCompute
      (FunctionOnInterval.exactRat (fun _ => (1 : Rat)) 0 1)
      (by decide +kernel)
      (fun _ => 1) (fun _ => 0)
      (by intro k; decide +kernel) n)
    { lo := 1, hi := 1 }
  rw [hcompute]
  constructor <;> decide +kernel

theorem exactRat_affine_nondecreasing {r c a b : Rat} (hr : 0 <= r) :
    NondecreasingOnInterval
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) := by
  intro x y hx hy hxy n
  change r * x + c <= r * y + c
  simpa only [Rat.add_comm] using
    (Rat.add_le_add_left (c := c)).2
      (Rat.mul_le_mul_of_nonneg_left hxy hr)

theorem exactRat_affine_nonincreasing {r c a b : Rat} (hr : r <= 0) :
    NonincreasingOnInterval
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) := by
  intro x y hx hy hxy n
  change r * y + c <= r * x + c
  have hmul := Rat.mul_le_mul_of_nonneg_left hxy (by grind : 0 <= -r)
  have hneg := Rat.neg_le_neg hmul
  simpa only [Rat.add_comm] using
    (Rat.add_le_add_left (c := c)).2
      (by grind [Rat.mul_neg, Rat.neg_mul] : r * y <= r * x)

def constantMonotoneCandidateConstructionFor (c a b : Rat) :
    MonotoneCandidateConstructionFor
      (FunctionOnInterval.exactRat (fun _ => c) a b) where
  monotone := MonotoneOnInterval.ofNondecreasing
    (exactRat_constant_nondecreasing c a b)
  construction :=
    { compute := (RealCompute.ofRat ((b - a) * c)).compute
      certificate := RealCompute.ofRat_valid ((b - a) * c) }

namespace MonotoneCandidateConstructionFor

def restrict {F : FunctionOnInterval}
    (c : MonotoneCandidateConstructionFor F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    MonotoneCandidateConstructionFor (F.restrict a b hlo hab hhi) where
  monotone := c.monotone.restrict hlo hab hhi
  construction :=
    { compute := c.construction.compute
      certificate := c.construction.certificate }

end MonotoneCandidateConstructionFor

/-- The preferred first case for integrals: a certified nondecreasing
function together with its valid integral construction. -/
structure NondecreasingCandidateConstructionFor (F : FunctionOnInterval) where
  nondecreasing : NondecreasingOnInterval F
  construction : CandidateConstructionFor F

namespace NondecreasingCandidateConstructionFor

def toMonotoneCandidateConstructionFor {F : FunctionOnInterval}
    (c : NondecreasingCandidateConstructionFor F) :
    MonotoneCandidateConstructionFor F where
  monotone := MonotoneOnInterval.ofNondecreasing c.nondecreasing
  construction := c.construction

def restrict {F : FunctionOnInterval}
    (c : NondecreasingCandidateConstructionFor F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    NondecreasingCandidateConstructionFor (F.restrict a b hlo hab hhi) where
  nondecreasing := c.nondecreasing.restrict hlo hab hhi
  construction :=
    { compute := c.construction.compute
      certificate := c.construction.certificate }

end NondecreasingCandidateConstructionFor

def monotoneCandidateValueFor (F : FunctionOnInterval)
    (c : MonotoneCandidateConstructionFor F) : RealCompute :=
  candidateValueFor F c.construction

theorem monotoneCandidateValueFor_valid (F : FunctionOnInterval)
    (c : MonotoneCandidateConstructionFor F) :
    (monotoneCandidateValueFor F c).Valid :=
  candidateValueFor_valid F c.construction

theorem constantMonotoneCandidateValueFor_eq_ofRat (c a b : Rat) :
    monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun _ => c) a b)
      (constantMonotoneCandidateConstructionFor c a b) =
      RealCompute.ofRat ((b - a) * c) := by
  rfl

def ExistsMonotoneCandidateConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (MonotoneCandidateConstructionFor F)

theorem exists_constantMonotoneCandidateConstructionFor (c a b : Rat) :
    ExistsMonotoneCandidateConstructionFor
      (FunctionOnInterval.exactRat (fun _ => c) a b) := by
  exact ⟨constantMonotoneCandidateConstructionFor c a b⟩

def affineMonotoneCandidateConstructionFor {r c a b : Rat} (hr : 0 <= r) :
    MonotoneCandidateConstructionFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  monotone := MonotoneOnInterval.ofNondecreasing
    (exactRat_affine_nondecreasing hr)
  construction :=
    { compute :=
        (RealCompute.ofRat
          ((b - a) * (r * (a + b) / 2 + c))).compute
      certificate := RealCompute.ofRat_valid
        ((b - a) * (r * (a + b) / 2 + c)) }

def affineMonotoneCandidateConstructionFor_of_nonpos {r c a b : Rat} (hr : r <= 0) :
    MonotoneCandidateConstructionFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  monotone := MonotoneOnInterval.ofNonincreasing
    (exactRat_affine_nonincreasing hr)
  construction :=
    { compute :=
        (RealCompute.ofRat
          ((b - a) * (r * (a + b) / 2 + c))).compute
      certificate := RealCompute.ofRat_valid
        ((b - a) * (r * (a + b) / 2 + c)) }

theorem exists_affineMonotoneCandidateConstructionFor {r c a b : Rat} (hr : 0 <= r) :
    ExistsMonotoneCandidateConstructionFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) := by
  exact ⟨affineMonotoneCandidateConstructionFor hr⟩

theorem exists_affineMonotoneCandidateConstructionFor_of_nonpos
    {r c a b : Rat} (hr : r <= 0) :
    ExistsMonotoneCandidateConstructionFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) := by
  exact ⟨affineMonotoneCandidateConstructionFor_of_nonpos hr⟩

/-! The first nonconstant adjacent-interval additivity theorem.  The affine
construction is an exact rational endpoint formula, so the proof is finite
ring algebra followed by raw-interval overlap. -/

theorem affineMonotoneCandidateValueFor_adjacent_additive
    {r c a b d : Rat} (hr : 0 <= r) :
    (monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a d)
      (affineMonotoneCandidateConstructionFor (r := r) (c := c) (a := a) (b := d) hr)).Equiv
      { compute := RealCompute.addCompute
          (monotoneCandidateValueFor
            (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
            (affineMonotoneCandidateConstructionFor (r := r) (c := c) (a := a) (b := b) hr))
          (monotoneCandidateValueFor
            (FunctionOnInterval.exactRat (fun x => r * x + c) b d)
            (affineMonotoneCandidateConstructionFor (r := r) (c := c) (a := b) (b := d) hr)) } := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a d)
      (affineMonotoneCandidateConstructionFor (r := r) (c := c) (a := a) (b := d) hr)).compute n)
    (RealCompute.addCompute
      (monotoneCandidateValueFor
        (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
        (affineMonotoneCandidateConstructionFor (r := r) (c := c) (a := a) (b := b) hr))
      (monotoneCandidateValueFor
        (FunctionOnInterval.exactRat (fun x => r * x + c) b d)
        (affineMonotoneCandidateConstructionFor (r := r) (c := c) (a := b) (b := d) hr)) n)
  simp [monotoneCandidateValueFor, candidateValueFor, affineMonotoneCandidateConstructionFor,
    RealCompute.ofRat, RealCompute.addCompute, QInterval.Overlaps]
  constructor <;> grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem affineMonotoneCandidateValueFor_of_nonpos_adjacent_additive
    {r c a b d : Rat} (hr : r <= 0) :
    (monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a d)
      (affineMonotoneCandidateConstructionFor_of_nonpos
        (r := r) (c := c) (a := a) (b := d) hr)).Equiv
      { compute := RealCompute.addCompute
          (monotoneCandidateValueFor
            (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
            (affineMonotoneCandidateConstructionFor_of_nonpos
              (r := r) (c := c) (a := a) (b := b) hr))
          (monotoneCandidateValueFor
            (FunctionOnInterval.exactRat (fun x => r * x + c) b d)
            (affineMonotoneCandidateConstructionFor_of_nonpos
              (r := r) (c := c) (a := b) (b := d) hr)) } := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a d)
      (affineMonotoneCandidateConstructionFor_of_nonpos
        (r := r) (c := c) (a := a) (b := d) hr)).compute n)
    (RealCompute.addCompute
      (monotoneCandidateValueFor
        (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
        (affineMonotoneCandidateConstructionFor_of_nonpos
          (r := r) (c := c) (a := a) (b := b) hr))
      (monotoneCandidateValueFor
        (FunctionOnInterval.exactRat (fun x => r * x + c) b d)
        (affineMonotoneCandidateConstructionFor_of_nonpos
          (r := r) (c := c) (a := b) (b := d) hr)) n)
  simp [monotoneCandidateValueFor, candidateValueFor,
    affineMonotoneCandidateConstructionFor_of_nonpos, RealCompute.ofRat,
    RealCompute.addCompute, QInterval.Overlaps]
  constructor <;> grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem affineMonotoneCandidateValueFor_eq_ofRat {r c a b : Rat} (hr : 0 <= r) :
    monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (affineMonotoneCandidateConstructionFor hr) =
      RealCompute.ofRat ((b - a) * (r * (a + b) / 2 + c)) := by
  rfl

theorem unitMeshSquareIntegralRaw_equiv_affineMonotoneIntegral :
    unitMeshSquareIntegralRaw.Equiv
      (monotoneCandidateValueFor
        (FunctionOnInterval.exactRat (fun x : Rat => 2 * x + 0) 0 1)
        (affineMonotoneCandidateConstructionFor
          (r := 2) (c := 0) (a := 0) (b := 1) (by decide +kernel))) := by
  rw [affineMonotoneCandidateValueFor_eq_ofRat]
  · have hone :
        ((1 : Rat) - 0) * (2 * (0 + 1) / 2 + 0) = 1 := by decide +kernel
    rw [hone]
    exact unitMeshSquareIntegralRaw_equiv_one

theorem affineMonotoneCandidateValueFor_of_nonpos_eq_ofRat
    {r c a b : Rat} (hr : r <= 0) :
    monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (affineMonotoneCandidateConstructionFor_of_nonpos hr) =
      RealCompute.ofRat ((b - a) * (r * (a + b) / 2 + c)) := by
  rfl

def nondecreasingCandidateValueFor (F : FunctionOnInterval)
    (c : NondecreasingCandidateConstructionFor F) : RealCompute :=
  candidateValueFor F c.construction

theorem nondecreasingCandidateValueFor_valid (F : FunctionOnInterval)
    (c : NondecreasingCandidateConstructionFor F) :
    (nondecreasingCandidateValueFor F c).Valid :=
  candidateValueFor_valid F c.construction

theorem nondecreasingCandidateValueFor_eq_monotoneCandidateValueFor
    (F : FunctionOnInterval) (c : NondecreasingCandidateConstructionFor F) :
    nondecreasingCandidateValueFor F c =
      monotoneCandidateValueFor F c.toMonotoneCandidateConstructionFor := rfl

def ExistsNondecreasingCandidateConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (NondecreasingCandidateConstructionFor F)

/-- A piecewise-monotone integral plan: split an interval into finitely many
rational subintervals and supply a monotone construction on each piece. -/
structure PiecewiseMonotoneCandidateConstructionFor (F : FunctionOnInterval) where
  pieces : Nat
  positive : 0 < pieces
  point : Nat -> Rat
  left_endpoint : point 0 = F.lower
  right_endpoint : point pieces = F.upper
  point_mem :
    forall i, i <= pieces -> inDomainInterval F.lower F.upper (point i)
  point_mono :
    forall i j, i <= j -> j <= pieces -> point i <= point j
  construction :
    forall k (hk : k < pieces),
      MonotoneCandidateConstructionFor
        (F.restrict (point k) (point (k + 1))
          (point_mem k (Nat.le_of_lt hk)).1
          (point_mono k (k + 1) (Nat.le_succ k) (Nat.succ_le_of_lt hk))
          (point_mem (k + 1) (Nat.succ_le_of_lt hk)).2)

namespace PiecewiseMonotoneCandidateConstructionFor

/-- Promote one monotone integral construction to the general piecewise
interface by using the one-cell partition `[lower, upper]`. -/
noncomputable def ofMonotone {F : FunctionOnInterval}
    (c : MonotoneCandidateConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    PiecewiseMonotoneCandidateConstructionFor F where
  pieces := 1
  positive := by decide
  point
    | 0 => F.lower
    | _ + 1 => F.upper
  left_endpoint := rfl
  right_endpoint := rfl
  point_mem := by
    intro i _hi
    cases i with
    | zero =>
        exact ⟨Rat.le_refl, hinterval⟩
    | succ _ =>
        exact ⟨hinterval, Rat.le_refl⟩
  point_mono := by
    intro i j hij _hj
    cases i with
    | zero =>
        cases j with
        | zero =>
            exact Rat.le_refl
        | succ _ =>
            exact hinterval
    | succ i' =>
        cases j with
        | zero =>
            exact False.elim (Nat.not_succ_le_zero i' hij)
        | succ _ =>
            exact Rat.le_refl
  construction := by
    intro k hk
    have hk_le_zero : k <= 0 := Nat.le_of_lt_succ hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk_le_zero
    subst k
    simpa using
      c.restrict
        Rat.le_refl
        hinterval
        Rat.le_refl

/-- Promote the preferred nondecreasing integral construction to the general
piecewise interface. -/
noncomputable def ofNondecreasing {F : FunctionOnInterval}
    (c : NondecreasingCandidateConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    PiecewiseMonotoneCandidateConstructionFor F :=
  ofMonotone c.toMonotoneCandidateConstructionFor hinterval

end PiecewiseMonotoneCandidateConstructionFor

/-- The integral raw real for a single monotone piece of a piecewise-monotone
construction. -/
def piecewiseMonotoneCellIntegral (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F)
    (k : Nat) (hk : k < c.pieces) : RealCompute :=
  monotoneCandidateValueFor _ (c.construction k hk)

/-! The finite cell list follows the same `List.range` order as the public
fold.  Each entry still carries its cell-index proof locally, while the list
shape remains directly compatible with finite fold algebra. -/
def piecewiseMonotoneCellList (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) : List RealCompute :=
  (List.range c.pieces).map (fun k =>
    if hk : k < c.pieces then
      piecewiseMonotoneCellIntegral F c k hk
    else RealCompute.zero)

theorem piecewiseMonotoneCellList_length (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) :
    (piecewiseMonotoneCellList F c).length = c.pieces := by
  simp [piecewiseMonotoneCellList]

theorem piecewiseMonotoneCellList_ne_nil (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) :
    piecewiseMonotoneCellList F c ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [piecewiseMonotoneCellList] at hlength
  have hp := c.positive
  omega

theorem piecewiseMonotoneCellIntegral_valid (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F)
    (k : Nat) (hk : k < c.pieces) :
  (piecewiseMonotoneCellIntegral F c k hk).Valid :=
  monotoneCandidateValueFor_valid _ (c.construction k hk)

theorem piecewiseMonotoneCellList_valid (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) :
    forall x, x ∈ piecewiseMonotoneCellList F c -> x.Valid := by
  intro x hx
  rcases List.mem_map.1 hx with ⟨k, _hk, rfl⟩
  have hk : k < c.pieces := List.mem_range.1 _hk
  simp [hk]
  exact piecewiseMonotoneCellIntegral_valid F c k hk

theorem piecewiseMonotoneCellList_finiteRawSum_valid
    (F : FunctionOnInterval) (c : PiecewiseMonotoneCandidateConstructionFor F) :
    (finiteRawSum (piecewiseMonotoneCellList F c)).Valid :=
  finiteRawSum_valid _ (piecewiseMonotoneCellList_valid F c)

/-- Sum the monotone-piece integrals over the finite rational partition. -/
def piecewiseMonotoneCandidateValueFor (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) : RealCompute :=
  (List.range c.pieces).foldl
    (fun acc k => acc +
      if hk : k < c.pieces then
        piecewiseMonotoneCellIntegral F c k hk
      else RealCompute.zero)
    (RealCompute.ofRat 0)

theorem piecewiseMonotoneCandidateValueFor_valid (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) :
    (piecewiseMonotoneCandidateValueFor F c).Valid := by
  let step : RealCompute -> Nat -> RealCompute :=
    fun acc k =>
      acc + if hk : k < c.pieces then
        piecewiseMonotoneCellIntegral F c k hk
      else RealCompute.zero
  have hstep : forall acc k, acc.Valid -> (step acc k).Valid := by
    intro acc k hacc
    by_cases hk : k < c.pieces
    · simp [step, hk]
      exact RealCompute.add_valid hacc
        (piecewiseMonotoneCellIntegral_valid F c k hk)
    · simp [step, hk, hacc]
      exact RealCompute.add_valid hacc (by
        change (RealCompute.zero).Valid
        exact RealCompute.ofRat_valid 0)
  have hfold :
      forall (xs : List Nat) (acc : RealCompute),
        acc.Valid -> (xs.foldl step acc).Valid := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons k ks ih =>
        intro acc hacc
        simpa [List.foldl] using ih (step acc k) (hstep acc k hacc)
  simpa [piecewiseMonotoneCandidateValueFor, step] using
    hfold (List.range c.pieces) (RealCompute.ofRat 0) (by
    simpa [RealCompute.Valid, RealCompute.ofRat] using RealCompute.ofRat_valid 0)

/-! The two-cell case is the first reusable finite assembly law.  It exposes
the piecewise fold as the sum of its two certified cell integrals, up to the
interval-representative equivalence. -/
theorem piecewiseMonotoneCandidateValueFor_two_equiv
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F)
    (hpieces : c.pieces = 2) :
    (piecewiseMonotoneCandidateValueFor F c).Equiv
      (piecewiseMonotoneCellIntegral F c 0 (by omega) +
        piecewiseMonotoneCellIntegral F c 1 (by omega)) := by
  have h0 : (piecewiseMonotoneCellIntegral F c 0 (by omega)).Valid :=
    piecewiseMonotoneCellIntegral_valid F c 0 (by omega)
  have h1 : (piecewiseMonotoneCellIntegral F c 1 (by omega)).Valid :=
    piecewiseMonotoneCellIntegral_valid F c 1 (by omega)
  have hzero : (RealCompute.zero).Valid := by
    change RealCompute.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
    exact RealCompute.ofRat_valid 0
  have hsum :
      (piecewiseMonotoneCellIntegral F c 0 (by omega) +
        piecewiseMonotoneCellIntegral F c 1 (by omega)).Valid :=
    RealCompute.add_valid h0 h1
  have hleft :
      ((RealCompute.zero + piecewiseMonotoneCellIntegral F c 0 (by omega)) +
        piecewiseMonotoneCellIntegral F c 1 (by omega)).Valid :=
    RealCompute.add_valid (RealCompute.add_valid hzero h0) h1
  have hmid :
      (RealCompute.zero +
        (piecewiseMonotoneCellIntegral F c 0 (by omega) +
          piecewiseMonotoneCellIntegral F c 1 (by omega))).Valid :=
    RealCompute.add_valid hzero hsum
  have hassoc := RealCompute.add_assoc_equiv
    RealCompute.zero
    (piecewiseMonotoneCellIntegral F c 0 (by omega))
    (piecewiseMonotoneCellIntegral F c 1 (by omega))
    hzero h0 h1
  have hzeroadd := RealCompute.zero_add_equiv hsum
  have hfold :
      ((RealCompute.zero + piecewiseMonotoneCellIntegral F c 0 (by omega)) +
          piecewiseMonotoneCellIntegral F c 1 (by omega)).Equiv
        (piecewiseMonotoneCellIntegral F c 0 (by omega) +
          piecewiseMonotoneCellIntegral F c 1 (by omega)) := by
    exact RealCompute.equiv_trans hleft hmid hsum hassoc hzeroadd
  unfold piecewiseMonotoneCandidateValueFor
  simp only [hpieces]
  have hrange : List.range 2 = [0, 1] := by decide +kernel
  rw [hrange]
  simpa [RealCompute.zero, RealCompute.ofRat] using hfold

/-! The arbitrary finite version of the two-cell assembly law.  The public
piecewise fold and the canonical finite raw sum differ only by parenthesizing
addition; the proof is a finite induction and introduces no limiting object. -/
theorem piecewiseMonotoneCandidateValueFor_equiv_finiteRawSum
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) :
    (piecewiseMonotoneCandidateValueFor F c).Equiv
      (finiteRawSum (piecewiseMonotoneCellList F c)) := by
  let cell : Nat -> RealCompute := fun k =>
    if hk : k < c.pieces then
      piecewiseMonotoneCellIntegral F c k hk
    else RealCompute.zero
  let step : RealCompute -> Nat -> RealCompute := fun acc k => acc + cell k
  have hcell : forall k, k < c.pieces -> (cell k).Valid := by
    intro k hk
    simp [cell, hk]
    exact piecewiseMonotoneCellIntegral_valid F c k hk
  have hzero : (RealCompute.zero).Valid := by
    change RealCompute.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
    exact RealCompute.ofRat_valid 0
  have hsum_valid : forall (xs : List RealCompute),
      (forall x, x ∈ xs -> x.Valid) -> (finiteRawSum xs).Valid :=
    finiteRawSum_valid
  have hstep_valid : forall (xs : List Nat) (acc : RealCompute),
      acc.Valid -> (xs.foldl step acc).Valid := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons k ks ih =>
        intro acc hacc
        apply ih
        exact RealCompute.add_valid hacc (by
          by_cases hk : k < c.pieces
          · exact hcell k hk
          · simp [cell, hk]
            exact hzero)
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < c.pieces) ->
      forall (acc : RealCompute), acc.Valid ->
        (xs.foldl step acc).Equiv
          (acc + finiteRawSum (xs.map cell)) := by
    intro xs
    induction xs with
    | nil =>
        intro _ acc hacc
        simpa [finiteRawSum] using
          (RealCompute.equiv_symm (RealCompute.add_zero_equiv hacc))
    | cons k ks ih =>
        intro hxs acc hacc
        have hk : k < c.pieces := hxs k (by simp)
        have htail : forall j, j ∈ ks -> j < c.pieces := by
          intro j hj
          exact hxs j (by simp [hj])
        have hck : (cell k).Valid := hcell k hk
        have hacc' : (acc + cell k).Valid := RealCompute.add_valid hacc hck
        have htailSum : (finiteRawSum (ks.map cell)).Valid := by
          apply hsum_valid
          intro x hx
          rcases List.mem_map.1 hx with ⟨j, hj, rfl⟩
          exact hcell j (htail j hj)
        have hih := ih htail (acc + cell k) hacc'
        have hassoc := RealCompute.add_assoc_equiv acc (cell k)
          (finiteRawSum (ks.map cell)) hacc hck htailSum
        have hleft :
            (ks.foldl step (acc + cell k)).Valid :=
          hstep_valid ks (acc + cell k) hacc'
        have hright :
            (acc + (cell k + finiteRawSum (ks.map cell))).Valid :=
          RealCompute.add_valid hacc (RealCompute.add_valid hck htailSum)
        simpa [List.foldl, step, finiteRawSum] using
          (RealCompute.equiv_trans hleft
            (RealCompute.add_valid hacc' htailSum) hright hih hassoc)
  have hresult := hfold (List.range c.pieces)
    (by
      intro k hk
      exact List.mem_range.1 hk)
    RealCompute.zero hzero
  have hleft :
      ((List.range c.pieces).foldl step RealCompute.zero).Valid :=
    hstep_valid (List.range c.pieces) RealCompute.zero hzero
  have hsum :
      (finiteRawSum ((List.range c.pieces).map cell)).Valid := by
    apply hsum_valid
    intro x hx
    rcases List.mem_map.1 hx with ⟨k, hk, rfl⟩
    exact hcell k (List.mem_range.1 hk)
  have hclean :
      ((List.range c.pieces).foldl step RealCompute.zero).Equiv
        (finiteRawSum ((List.range c.pieces).map cell)) := by
    exact RealCompute.equiv_trans hleft
      (RealCompute.add_valid hzero hsum) hsum hresult
      (RealCompute.zero_add_equiv hsum)
  simpa [piecewiseMonotoneCandidateValueFor, piecewiseMonotoneCellList,
    cell, step, RealCompute.zero] using hclean

/-! A cell endpoint difference is the raw subtraction of the two endpoint
evaluators.  Its validity follows directly from the interval function's
pointwise validity; no global real-valued function or completeness principle
is involved. -/
def piecewiseMonotoneEndpointDifference
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F)
    (k : Nat) (hk : k < c.pieces) : RealCompute :=
  (F.raw.evalRaw (c.point (k + 1))
      (F.defined_on (c.point (k + 1))
        (c.point_mem (k + 1) (Nat.succ_le_of_lt hk))) -
    F.raw.evalRaw (c.point k)
      (F.defined_on (c.point k)
        (c.point_mem k (Nat.le_of_lt hk))))

theorem piecewiseMonotoneEndpointDifference_valid
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F)
    (k : Nat) (hk : k < c.pieces) :
    (piecewiseMonotoneEndpointDifference F c k hk).Valid := by
  let hx := c.point_mem k (Nat.le_of_lt hk)
  let hy := c.point_mem (k + 1) (Nat.succ_le_of_lt hk)
  let x := F.raw.evalRaw (c.point k) (F.defined_on (c.point k) hx)
  let y := F.raw.evalRaw (c.point (k + 1)) (F.defined_on (c.point (k + 1)) hy)
  have hvalidx : x.Valid := by
    simpa [x, RealCompute.Valid, PartialRealFunRaw.evalRaw] using
      F.valid_on (c.point k) (F.defined_on (c.point k) hx)
  have hvalidy : y.Valid := by
    simpa [y, RealCompute.Valid, PartialRealFunRaw.evalRaw] using
      F.valid_on (c.point (k + 1)) (F.defined_on (c.point (k + 1)) hy)
  simpa [piecewiseMonotoneEndpointDifference, x, y, hx, hy] using
    RealCompute.sub_valid hvalidy hvalidx

def piecewiseMonotoneEndpointDifferenceList
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) : List RealCompute :=
  (List.range c.pieces).map (fun k =>
    if hk : k < c.pieces then
      piecewiseMonotoneEndpointDifference F c k hk
    else RealCompute.zero)

theorem piecewiseMonotoneEndpointDifferenceList_length
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) :
    (piecewiseMonotoneEndpointDifferenceList F c).length = c.pieces := by
  simp [piecewiseMonotoneEndpointDifferenceList]

structure PiecewiseMonotoneEndpointFTCFor
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) where
  cell_endpoint_equiv :
    forall k (hk : k < c.pieces),
      (piecewiseMonotoneCellIntegral F c k hk).Equiv
        (piecewiseMonotoneEndpointDifference F c k hk)

theorem piecewiseMonotoneCandidateValueFor_equiv_endpointDifferenceList
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F)
    (h : PiecewiseMonotoneEndpointFTCFor F c) :
    (piecewiseMonotoneCandidateValueFor F c).Equiv
      (finiteRawSum (piecewiseMonotoneEndpointDifferenceList F c)) := by
  let cell : Nat -> RealCompute := fun k =>
    if hk : k < c.pieces then
      piecewiseMonotoneCellIntegral F c k hk
    else RealCompute.zero
  let endpoint : Nat -> RealCompute := fun k =>
    if hk : k < c.pieces then
      piecewiseMonotoneEndpointDifference F c k hk
    else RealCompute.zero
  have hlist_aux : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < c.pieces) ->
      FiniteRawListEquiv (xs.map cell) (xs.map endpoint) := by
    intro xs
    induction xs with
    | nil =>
        intro _
        exact .nil
    | cons k ks ih =>
        intro hxs
        have hk : k < c.pieces := hxs k (by simp)
        have htail : forall j, j ∈ ks -> j < c.pieces := by
          intro j hj
          exact hxs j (by simp [hj])
        apply FiniteRawListEquiv.cons
        · simp [cell, endpoint, hk]
          exact h.cell_endpoint_equiv k hk
        · exact ih htail
  have hlist := hlist_aux (List.range c.pieces)
    (by
      intro k hk
      exact List.mem_range.1 hk)
  have hcell : forall x, x ∈ (List.range c.pieces).map cell -> x.Valid := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨k, hk, rfl⟩
    simp [cell, List.mem_range.1 hk]
    exact piecewiseMonotoneCellIntegral_valid F c k (List.mem_range.1 hk)
  have hendpoint : forall x,
      x ∈ (List.range c.pieces).map endpoint -> x.Valid := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨k, hk, rfl⟩
    simp [endpoint, List.mem_range.1 hk]
    exact piecewiseMonotoneEndpointDifference_valid F c k (List.mem_range.1 hk)
  have hsum := finiteRawSum_equiv_of_forall hlist hcell hendpoint
  have hintegral := piecewiseMonotoneCandidateValueFor_equiv_finiteRawSum F c
  have hleft : (piecewiseMonotoneCandidateValueFor F c).Valid :=
    piecewiseMonotoneCandidateValueFor_valid F c
  have hmiddle :
      (finiteRawSum ((List.range c.pieces).map cell)).Valid :=
    finiteRawSum_valid _ hcell
  have hright :
      (finiteRawSum ((List.range c.pieces).map endpoint)).Valid :=
    finiteRawSum_valid _ hendpoint
  have hresult := RealCompute.equiv_trans hleft hmiddle hright hintegral hsum
  simpa [piecewiseMonotoneCellList, piecewiseMonotoneEndpointDifferenceList,
    cell, endpoint] using hresult

def piecewiseMonotoneTotalEndpointDifference
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) : RealCompute :=
  F.raw.evalRaw (c.point c.pieces)
      (F.defined_on (c.point c.pieces)
        (c.point_mem c.pieces (Nat.le_refl _))) -
    F.raw.evalRaw (c.point 0)
      (F.defined_on (c.point 0)
        (c.point_mem 0 (Nat.zero_le _)))

theorem piecewiseMonotoneTotalEndpointDifference_valid
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F) :
    (piecewiseMonotoneTotalEndpointDifference F c).Valid := by
  let hx := c.point_mem 0 (Nat.zero_le _)
  let hy := c.point_mem c.pieces (Nat.le_refl _)
  let x := F.raw.evalRaw (c.point 0) (F.defined_on (c.point 0) hx)
  let y := F.raw.evalRaw (c.point c.pieces) (F.defined_on (c.point c.pieces) hy)
  have hvalidx : x.Valid := by
    simpa [x, RealCompute.Valid, PartialRealFunRaw.evalRaw] using
      F.valid_on (c.point 0) (F.defined_on (c.point 0) hx)
  have hvalidy : y.Valid := by
    simpa [y, RealCompute.Valid, PartialRealFunRaw.evalRaw] using
      F.valid_on (c.point c.pieces) (F.defined_on (c.point c.pieces) hy)
  simpa [piecewiseMonotoneTotalEndpointDifference, x, y, hx, hy] using
    RealCompute.sub_valid hvalidy hvalidx

/-! Compose the piecewise cell certificate with the domain-independent raw
telescoping theorem.  The explicit list-transport hypothesis is the finite
geometric bookkeeping still required to identify the interval's endpoint
evaluators with adjacent entries; the theorem itself contains no completeness
or limiting argument. -/
theorem piecewiseMonotoneCandidateValueFor_equiv_totalEndpointDifference_of_telescope
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneCandidateConstructionFor F)
    (h : PiecewiseMonotoneEndpointFTCFor F c)
    {first : RealCompute} {rest : List RealCompute}
    (hvalues : forall x, x ∈ first :: rest -> x.Valid)
    (htransport :
      FiniteRawListEquiv
        (piecewiseMonotoneEndpointDifferenceList F c)
        (rawAdjacentDifferenceList (first :: rest)))
    (htotal : (rawLast first rest - first).Equiv
      (piecewiseMonotoneTotalEndpointDifference F c)) :
    (piecewiseMonotoneCandidateValueFor F c).Equiv
      (piecewiseMonotoneTotalEndpointDifference F c) := by
  have hendpoint : forall x,
      x ∈ piecewiseMonotoneEndpointDifferenceList F c -> x.Valid := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨k, hk, rfl⟩
    have hk' : k < c.pieces := List.mem_range.1 hk
    simp [piecewiseMonotoneEndpointDifferenceList, hk']
    exact piecewiseMonotoneEndpointDifference_valid F c k hk'
  have hadjacent : forall x,
      x ∈ rawAdjacentDifferenceList (first :: rest) -> x.Valid :=
    rawAdjacentDifferenceList_valid hvalues
  have hsum_endpoint := finiteRawSum_valid
    (piecewiseMonotoneEndpointDifferenceList F c) hendpoint
  have hsum_adjacent := finiteRawSum_valid
    (rawAdjacentDifferenceList (first :: rest)) hadjacent
  have htransport_sum := finiteRawSum_equiv_of_forall
    htransport hendpoint hadjacent
  have htel := finiteRawSum_rawAdjacentDifferenceList_equiv_last_sub_first
    hvalues
  have hlast : (rawLast first rest).Valid := rawLast_valid hvalues
  have hfirst : first.Valid := hvalues first (by simp)
  have hsub : (rawLast first rest - first).Valid :=
    RealCompute.sub_valid hlast hfirst
  have htotal_valid := piecewiseMonotoneTotalEndpointDifference_valid F c
  have hcell := piecewiseMonotoneCandidateValueFor_equiv_endpointDifferenceList F c h
  have hintegral := piecewiseMonotoneCandidateValueFor_valid F c
  have hintegral_adjacent :
      (piecewiseMonotoneCandidateValueFor F c).Equiv
        (finiteRawSum (rawAdjacentDifferenceList (first :: rest))) :=
    RealCompute.equiv_trans hintegral hsum_endpoint hsum_adjacent hcell
      htransport_sum
  have hadjacent_total :
      (finiteRawSum (rawAdjacentDifferenceList (first :: rest))).Equiv
        (piecewiseMonotoneTotalEndpointDifference F c) :=
    RealCompute.equiv_trans hsum_adjacent hsub htotal_valid htel htotal
  exact RealCompute.equiv_trans hintegral hsum_adjacent htotal_valid
    hintegral_adjacent hadjacent_total

/-- A one-piece promotion from a monotone construction computes the same raw
integral as the original monotone construction. -/
theorem piecewiseMonotoneCandidateValueFor_ofMonotone_equiv
    {F : FunctionOnInterval}
    (c : MonotoneCandidateConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (piecewiseMonotoneCandidateValueFor F
      (PiecewiseMonotoneCandidateConstructionFor.ofMonotone c hinterval)).Equiv
        (monotoneCandidateValueFor F c) := by
  simpa [piecewiseMonotoneCandidateValueFor, piecewiseMonotoneCellIntegral,
    PiecewiseMonotoneCandidateConstructionFor.ofMonotone,
    MonotoneCandidateConstructionFor.restrict, monotoneCandidateValueFor, candidateValueFor,
    RealCompute.zero] using
    (RealCompute.zero_add_equiv
      (monotoneCandidateValueFor_valid F c))

/-- The preferred nondecreasing one-piece promotion is compatible with the
general piecewise-monotone integral. -/
theorem piecewiseMonotoneCandidateValueFor_ofNondecreasing_equiv
    {F : FunctionOnInterval}
    (c : NondecreasingCandidateConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (piecewiseMonotoneCandidateValueFor F
      (PiecewiseMonotoneCandidateConstructionFor.ofNondecreasing c hinterval)).Equiv
        (nondecreasingCandidateValueFor F c) := by
  simpa [PiecewiseMonotoneCandidateConstructionFor.ofNondecreasing,
    NondecreasingCandidateConstructionFor.toMonotoneCandidateConstructionFor,
    nondecreasingCandidateValueFor, monotoneCandidateValueFor] using
    (piecewiseMonotoneCandidateValueFor_ofMonotone_equiv
      (F := F) c.toMonotoneCandidateConstructionFor hinterval)

def ExistsPiecewiseMonotoneCandidateConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (PiecewiseMonotoneCandidateConstructionFor F)

/-- The legacy finite-piece numerical construction interface. This is not
the mathematical definition of a general integral; use `HasIntegral` for it.
The finite computations sum candidates on monotone pieces. -/
abbrev GeneralCandidateConstructionFor (F : FunctionOnInterval) :=
  PiecewiseMonotoneCandidateConstructionFor F

def generalCandidateValueFor (F : FunctionOnInterval)
    (c : GeneralCandidateConstructionFor F) : RealCompute :=
  piecewiseMonotoneCandidateValueFor F c

theorem generalCandidateValueFor_valid (F : FunctionOnInterval)
    (c : GeneralCandidateConstructionFor F) :
    (generalCandidateValueFor F c).Valid :=
  piecewiseMonotoneCandidateValueFor_valid F c

/-! The general finite-piece integral is also available through the common
`CandidateConstructionFor` interface.  This is only a representation bridge: the
finite monotone partition and all cell certificates remain explicit inputs. -/
def generalCandidateConstructionFor (F : FunctionOnInterval)
    (c : GeneralCandidateConstructionFor F) : Integral.CandidateConstructionFor F where
  compute := (generalCandidateValueFor F c).compute
  certificate := generalCandidateValueFor_valid F c

theorem generalCandidateConstructionFor_compute_eq (F : FunctionOnInterval)
    (c : GeneralCandidateConstructionFor F) :
    (generalCandidateConstructionFor F c).compute = (generalCandidateValueFor F c).compute := rfl

theorem candidateValueFor_generalCandidateConstructionFor_valid (F : FunctionOnInterval)
    (c : GeneralCandidateConstructionFor F) :
    (Integral.candidateValueFor F (generalCandidateConstructionFor F c)).Valid :=
  Integral.candidateValueFor_valid F (generalCandidateConstructionFor F c)

theorem candidateValueFor_generalCandidateConstructionFor_equiv (F : FunctionOnInterval)
    (c : GeneralCandidateConstructionFor F) :
    (Integral.candidateValueFor F (generalCandidateConstructionFor F c)).Equiv
      (generalCandidateValueFor F c) := by
  exact RealCompute.equiv_refl _ (generalCandidateValueFor_valid F c)

/-- The public general-integral alias agrees with the original monotone
construction on a one-piece partition. -/
theorem generalCandidateValueFor_ofMonotone_equiv
    {F : FunctionOnInterval}
    (c : MonotoneCandidateConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (generalCandidateValueFor F
      (PiecewiseMonotoneCandidateConstructionFor.ofMonotone c hinterval)).Equiv
        (monotoneCandidateValueFor F c) := by
  simpa [generalCandidateValueFor] using
    piecewiseMonotoneCandidateValueFor_ofMonotone_equiv
      (F := F) c hinterval

/-- The public general-integral alias agrees with the preferred
nondecreasing construction on a one-piece partition. -/
theorem generalCandidateValueFor_ofNondecreasing_equiv
    {F : FunctionOnInterval}
    (c : NondecreasingCandidateConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (generalCandidateValueFor F
      (PiecewiseMonotoneCandidateConstructionFor.ofNondecreasing c hinterval)).Equiv
        (nondecreasingCandidateValueFor F c) := by
  simpa [generalCandidateValueFor] using
    piecewiseMonotoneCandidateValueFor_ofNondecreasing_equiv
      (F := F) c hinterval

abbrev ExistsGeneralCandidateConstructionFor (F : FunctionOnInterval) : Prop :=
  ExistsPiecewiseMonotoneCandidateConstructionFor F

/-! Mathematical integral laws are specified in `IntegralSpecification`
using `HasIntegral`, never universally quantified over numerical candidates. -/

/-- Exact rational-cell order preservation for an integrand together with a
closed-form integral over rational cells.

This is the finite algebraic version of the order-preservation theorem for
integrals.  If `c` is a lower bound for `eval` on every rational point of
`[p,r]`, then `(r-p)*c` is a lower bound for the exact cell integral.  The
upper statement is analogous. -/
structure ExactCellOrderPreservation
    (eval : Rat -> Rat) (integralBetween : Rat -> Rat -> Rat)
    (a b : Rat) where
  lower_const :
    forall {p r c : Rat}, a <= p -> p <= r -> r <= b ->
      (forall {x : Rat}, p <= x -> x <= r -> c <= eval x) ->
        (r - p) * c <= integralBetween p r
  upper_const :
    forall {p r c : Rat}, a <= p -> p <= r -> r <= b ->
      (forall {x : Rat}, p <= x -> x <= r -> eval x <= c) ->
        integralBetween p r <= (r - p) * c

/-! The integral-average layer of the Mean Value story.  This is stated over
the rational endpoint quantity supplied by the cell certificate; no completed
real average or attainment claim is involved. -/

theorem ExactCellOrderPreservation.integral_average_between_bounds
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    {a b : Rat} (h : ExactCellOrderPreservation eval integralBetween a b)
    {p r lower upper : Rat}
    (hap : a <= p) (hpr : p < r) (hrb : r <= b)
    (hlower : forall {x : Rat}, p <= x -> x <= r -> lower <= eval x)
    (hupper : forall {x : Rat}, p <= x -> x <= r -> eval x <= upper) :
    lower <= integralBetween p r / (r - p) /\
      integralBetween p r / (r - p) <= upper := by
  have hlength : 0 < r - p := by
    grind [Rat.sub_eq_add_neg]
  have hinv : 0 <= (r - p)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hlength)
  have hlow := h.lower_const hap (Rat.le_of_lt hpr) hrb hlower
  have hupp := h.upper_const hap (Rat.le_of_lt hpr) hrb hupper
  have hlow' := Rat.mul_le_mul_of_nonneg_right hlow hinv
  have hupp' := Rat.mul_le_mul_of_nonneg_right hupp hinv
  have hcancel : (r - p)⁻¹ * (r - p) = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt hlength)
  have hcancel' : (r - p) * (r - p)⁻¹ = 1 := by
    rw [Rat.mul_comm, hcancel]
  constructor
  · simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm,
      hcancel, hcancel'] using hlow'
  · simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm,
      hcancel, hcancel'] using hupp'

/-! The finite MVT-shaped conclusion: the cell average is represented by a
rational point interval lying inside the certified derivative range.  This
records the classical "some intermediate value" idea as overlap of rational
boxes, without selecting an attained real point. -/
theorem ExactCellOrderPreservation.integral_average_overlaps_bounds
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    {a b : Rat} (h : ExactCellOrderPreservation eval integralBetween a b)
    {p r lower upper : Rat}
    (hap : a <= p) (hpr : p < r) (hrb : r <= b)
    (hlower : forall {x : Rat}, p <= x -> x <= r -> lower <= eval x)
    (hupper : forall {x : Rat}, p <= x -> x <= r -> eval x <= upper) :
    QInterval.Overlaps
      ({ lo := lower, hi := upper } : QInterval)
      ({ lo := integralBetween p r / (r - p),
          hi := integralBetween p r / (r - p) } : QInterval) := by
  have havg := h.integral_average_between_bounds
    hap hpr hrb hlower hupper
  exact ⟨havg.1, havg.2⟩

/-- Exact rational-cell order preservation for a constant integrand.

This is the base case for finite polynomial integral certificates: the exact
integral of the constant `k` over `[p,r]` is `(r-p) * k`.  It uses only the
order of rational multiplication, with no limiting or completeness argument.
-/
theorem exactCellOrderPreservation_constant (a b k : Rat) :
    ExactCellOrderPreservation (fun _ => k) (fun p r => (r - p) * k) a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    have hlen : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    have hck : c <= k :=
      hbound (Rat.le_refl : p <= p) hpr
    exact Rat.mul_le_mul_of_nonneg_left hck hlen
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    have hlen : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    have hkc : k <= c :=
      hbound (Rat.le_refl : p <= p) hpr
    exact Rat.mul_le_mul_of_nonneg_left hkc hlen

/-- Sum of the weights in a finite rational quadrature rule.  A pair stores a
relative node followed by its weight. -/
def quadratureWeightSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (_, weight) :: rest => weight + quadratureWeightSum rest

/-- Weighted evaluation sum for a finite rational quadrature rule on `[p,r]`.
The first component of each pair is its relative node in `[0,1]`. -/
def quadratureEvalSum (eval : Rat -> Rat) (p r : Rat) :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (node, weight) :: rest =>
      weight * eval (p + node * (r - p)) +
        quadratureEvalSum eval p r rest

private theorem quadratureWeightSum_mul_le_quadratureEvalSum
    {eval : Rat -> Rat} {p r c : Rat}
    (nodes : List (Rat × Rat))
    (hpr : p <= r)
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hbound : forall {x : Rat}, p <= x -> x <= r -> c <= eval x) :
    quadratureWeightSum nodes * c <= quadratureEvalSum eval p r nodes := by
  induction nodes with
  | nil =>
      simp [quadratureWeightSum, quadratureEvalSum]
  | cons pair rest ih =>
      rcases pair with ⟨node, weight⟩
      have hnode := hnodes (node, weight) (by simp)
      have hweight : 0 <= weight := hweights (node, weight) (by simp)
      have hlength : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have hnodePointLower : p <= p + node * (r - p) := by
        have hmul : 0 <= node * (r - p) := Rat.mul_nonneg hnode.1 hlength
        grind
      have hnodePointUpper : p + node * (r - p) <= r := by
        have hmul : node * (r - p) <= 1 * (r - p) :=
          Rat.mul_le_mul_of_nonneg_right hnode.2 hlength
        calc
          p + node * (r - p) <= p + 1 * (r - p) :=
            (Rat.add_le_add_left).2 hmul
          _ = r := by grind [Rat.sub_eq_add_neg]
      have hpoint : c <= eval (p + node * (r - p)) :=
        hbound hnodePointLower hnodePointUpper
      have hhead : weight * c <= weight * eval (p + node * (r - p)) :=
        Rat.mul_le_mul_of_nonneg_left hpoint hweight
      have htail := ih
        (fun other hmem => hnodes other (by simp [hmem]))
        (fun other hmem => hweights other (by simp [hmem]))
      simp [quadratureWeightSum, quadratureEvalSum]
      calc
        (weight + quadratureWeightSum rest) * c =
            weight * c + quadratureWeightSum rest * c := by
          grind [Rat.add_mul]
        _ <= weight * eval (p + node * (r - p)) +
            quadratureEvalSum eval p r rest := by
          calc
            weight * c + quadratureWeightSum rest * c <=
                weight * eval (p + node * (r - p)) +
                  quadratureWeightSum rest * c :=
              (Rat.add_le_add_right).2 hhead
            _ <= weight * eval (p + node * (r - p)) +
                quadratureEvalSum eval p r rest :=
              (Rat.add_le_add_left).2 htail

private theorem quadratureEvalSum_le_quadratureWeightSum_mul
    {eval : Rat -> Rat} {p r c : Rat}
    (nodes : List (Rat × Rat))
    (hpr : p <= r)
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hbound : forall {x : Rat}, p <= x -> x <= r -> eval x <= c) :
    quadratureEvalSum eval p r nodes <= quadratureWeightSum nodes * c := by
  induction nodes with
  | nil =>
      simp [quadratureWeightSum, quadratureEvalSum]
  | cons pair rest ih =>
      rcases pair with ⟨node, weight⟩
      have hnode := hnodes (node, weight) (by simp)
      have hweight : 0 <= weight := hweights (node, weight) (by simp)
      have hlength : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have hnodePointLower : p <= p + node * (r - p) := by
        have hmul : 0 <= node * (r - p) := Rat.mul_nonneg hnode.1 hlength
        grind
      have hnodePointUpper : p + node * (r - p) <= r := by
        have hmul : node * (r - p) <= 1 * (r - p) :=
          Rat.mul_le_mul_of_nonneg_right hnode.2 hlength
        calc
          p + node * (r - p) <= p + 1 * (r - p) :=
            (Rat.add_le_add_left).2 hmul
          _ = r := by grind [Rat.sub_eq_add_neg]
      have hpoint : eval (p + node * (r - p)) <= c :=
        hbound hnodePointLower hnodePointUpper
      have hhead : weight * eval (p + node * (r - p)) <= weight * c :=
        Rat.mul_le_mul_of_nonneg_left hpoint hweight
      have htail := ih
        (fun other hmem => hnodes other (by simp [hmem]))
        (fun other hmem => hweights other (by simp [hmem]))
      simp [quadratureWeightSum, quadratureEvalSum]
      calc
        weight * eval (p + node * (r - p)) +
            quadratureEvalSum eval p r rest <=
            weight * c + quadratureWeightSum rest * c := by
          calc
            weight * eval (p + node * (r - p)) +
                quadratureEvalSum eval p r rest <=
                weight * c + quadratureEvalSum eval p r rest :=
              (Rat.add_le_add_right).2 hhead
            _ <= weight * c + quadratureWeightSum rest * c :=
              (Rat.add_le_add_left).2 htail
        _ = (weight + quadratureWeightSum rest) * c := by
          grind [Rat.add_mul]

/-- A finite positive rational quadrature identity gives exact cell-order
preservation.  It applies to any finite rule whose nodes lie in `[0,1]`, whose
weights are nonnegative and sum to one, and whose formula is exact for the
specified integrand. -/
theorem exactCellOrderPreservation_of_positive_quadrature
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    (a b : Rat) (nodes : List (Rat × Rat))
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hsum : quadratureWeightSum nodes = 1)
    (hformula : forall p r : Rat,
      integralBetween p r = (r - p) * quadratureEvalSum eval p r nodes) :
    ExactCellOrderPreservation eval integralBetween a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    have hsumBound := quadratureWeightSum_mul_le_quadratureEvalSum
      nodes hpr hnodes hweights hbound
    have haverage : c <= quadratureEvalSum eval p r nodes := by
      simpa [hsum] using hsumBound
    have hlength : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    rw [hformula]
    exact Rat.mul_le_mul_of_nonneg_left haverage hlength
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    have hsumBound := quadratureEvalSum_le_quadratureWeightSum_mul
      nodes hpr hnodes hweights hbound
    have haverage : quadratureEvalSum eval p r nodes <= c := by
      simpa [hsum] using hsumBound
    have hlength : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    rw [hformula]
    exact Rat.mul_le_mul_of_nonneg_left haverage hlength

/-- A positive Boole quadrature identity gives exact cell-order preservation.

The five rational nodes are the endpoints and the quarter points of a cell.
For a polynomial for which the displayed identity is exact, a pointwise bound
at all rational points bounds its exact integral.  The proof is finite rational
arithmetic; it invokes neither a limit nor real-number completeness. -/
theorem exactCellOrderPreservation_of_boole
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    (a b : Rat)
    (hboole : forall p r : Rat,
      integralBetween p r =
        ((r - p) / 90) *
          (7 * eval p +
            32 * eval (p + (r - p) / 4) +
            12 * eval (p + (r - p) / 2) +
            32 * eval (p + 3 * (r - p) / 4) +
            7 * eval r)) :
    ExactCellOrderPreservation eval integralBetween a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    let L : Rat := r - p
    let q₁ : Rat := p + L / 4
    let q₂ : Rat := p + L / 2
    let q₃ : Rat := p + 3 * L / 4
    have hL0 : 0 <= L := by
      dsimp [L]
      grind [Rat.sub_eq_add_neg]
    have hq₁ : p <= q₁ /\ q₁ <= r := by
      constructor
      · dsimp [q₁]
        have hdiv : 0 <= L / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by decide +kernel)
        grind
      · dsimp [q₁, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₂ : p <= q₂ /\ q₂ <= r := by
      constructor
      · dsimp [q₂]
        have hdiv : 0 <= L / 2 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by decide +kernel)
        grind
      · dsimp [q₂, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₃ : p <= q₃ /\ q₃ <= r := by
      constructor
      · dsimp [q₃]
        have hthreeL : 0 <= 3 * L :=
          Rat.mul_nonneg (by decide +kernel) hL0
        have hdiv : 0 <= (3 * L) / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hthreeL (by decide +kernel)
        grind
      · dsimp [q₃, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hp : c <= eval p := hbound (Rat.le_refl : p <= p) hpr
    have h1 : c <= eval q₁ := hbound hq₁.1 hq₁.2
    have h2 : c <= eval q₂ := hbound hq₂.1 hq₂.2
    have h3 : c <= eval q₃ := hbound hq₃.1 hq₃.2
    have hr : c <= eval r := hbound hpr (Rat.le_refl : r <= r)
    have hsum :
        90 * c <= 7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r := by
      have h7p := Rat.mul_le_mul_of_nonneg_left hp
        (by decide +kernel : (0 : Rat) <= 7)
      have h32q1 := Rat.mul_le_mul_of_nonneg_left h1
        (by decide +kernel : (0 : Rat) <= 32)
      have h12q2 := Rat.mul_le_mul_of_nonneg_left h2
        (by decide +kernel : (0 : Rat) <= 12)
      have h32q3 := Rat.mul_le_mul_of_nonneg_left h3
        (by decide +kernel : (0 : Rat) <= 32)
      have h7r := Rat.mul_le_mul_of_nonneg_left hr
        (by decide +kernel : (0 : Rat) <= 7)
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    have hscale : 0 <= L / 90 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg hL0 (by decide +kernel)
    rw [hboole]
    change L * c <=
      (L / 90) *
        (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r)
    calc
      L * c = (L / 90) * (90 * c) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (L / 90) *
          (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
            32 * eval q₃ + 7 * eval r) :=
        Rat.mul_le_mul_of_nonneg_left hsum hscale
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    let L : Rat := r - p
    let q₁ : Rat := p + L / 4
    let q₂ : Rat := p + L / 2
    let q₃ : Rat := p + 3 * L / 4
    have hL0 : 0 <= L := by
      dsimp [L]
      grind [Rat.sub_eq_add_neg]
    have hq₁ : p <= q₁ /\ q₁ <= r := by
      constructor
      · dsimp [q₁]
        have hdiv : 0 <= L / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by decide +kernel)
        grind
      · dsimp [q₁, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₂ : p <= q₂ /\ q₂ <= r := by
      constructor
      · dsimp [q₂]
        have hdiv : 0 <= L / 2 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by decide +kernel)
        grind
      · dsimp [q₂, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₃ : p <= q₃ /\ q₃ <= r := by
      constructor
      · dsimp [q₃]
        have hthreeL : 0 <= 3 * L :=
          Rat.mul_nonneg (by decide +kernel) hL0
        have hdiv : 0 <= (3 * L) / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hthreeL (by decide +kernel)
        grind
      · dsimp [q₃, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hp : eval p <= c := hbound (Rat.le_refl : p <= p) hpr
    have h1 : eval q₁ <= c := hbound hq₁.1 hq₁.2
    have h2 : eval q₂ <= c := hbound hq₂.1 hq₂.2
    have h3 : eval q₃ <= c := hbound hq₃.1 hq₃.2
    have hr : eval r <= c := hbound hpr (Rat.le_refl : r <= r)
    have hsum :
        7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r <= 90 * c := by
      have h7p := Rat.mul_le_mul_of_nonneg_left hp
        (by decide +kernel : (0 : Rat) <= 7)
      have h32q1 := Rat.mul_le_mul_of_nonneg_left h1
        (by decide +kernel : (0 : Rat) <= 32)
      have h12q2 := Rat.mul_le_mul_of_nonneg_left h2
        (by decide +kernel : (0 : Rat) <= 12)
      have h32q3 := Rat.mul_le_mul_of_nonneg_left h3
        (by decide +kernel : (0 : Rat) <= 32)
      have h7r := Rat.mul_le_mul_of_nonneg_left hr
        (by decide +kernel : (0 : Rat) <= 7)
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    have hscale : 0 <= L / 90 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg hL0 (by decide +kernel)
    rw [hboole]
    change (L / 90) *
        (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r) <= L * c
    calc
      (L / 90) *
          (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
            32 * eval q₃ + 7 * eval r) <=
          (L / 90) * (90 * c) :=
        Rat.mul_le_mul_of_nonneg_left hsum hscale
      _ = L * c := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

end Integral

/-- Effective inverse separation.

This is the extra constructive ingredient beyond monotonicity.  It says that
when two rational inputs are separated by the supplied amount, their interval
values are separated enough to locate the inverse at the requested precision.
Without this, a monotone function can be too flat for an effective inverse
algorithm. -/
structure EffectiveInverseSeparation (F : FunctionOnInterval) where
  /-- The one monotone orientation for which the separation certificate is
  supplied.  Requiring both orientations would make every nonconstant
  function fail the interface. -/
  kind : MonotonicityKind
  inputPrecision : Nat -> Nat
  inputPrecision_pos : forall n, 0 < inputPrecision n
  outputPrecision : Nat -> Nat
  separated :
    forall x y
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y)
      n,
      x + (1 / ((inputPrecision n) : Rat)) <= y ->
        match kind with
        | .nondecreasing =>
            (F.compute x hx (outputPrecision n)).hi <
              (F.compute y hy (outputPrecision n)).lo
        | .nonincreasing =>
            (F.compute y hy (outputPrecision n)).hi <
              (F.compute x hx (outputPrecision n)).lo

/-! A gap-aware variant of inverse separation.  For many computable
functions, the precision needed to distinguish `F x` from `F y` depends on
the actual rational gap `y - x`; this is the natural interface for a search
algorithm that refines its input bracket while it runs. -/
structure GapAwareInverseSeparation (F : FunctionOnInterval) where
  kind : MonotonicityKind
  outputPrecision : forall {x y : Rat}, x < y -> Nat -> Nat
  separated :
    forall x y
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y)
      (hxy : x < y) (n : Nat),
      match kind with
      | .nondecreasing =>
          (F.compute x hx (outputPrecision hxy n)).hi <
            (F.compute y hy (outputPrecision hxy n)).lo
      | .nonincreasing =>
          (F.compute y hy (outputPrecision hxy n)).hi <
            (F.compute x hx (outputPrecision hxy n)).lo

/-- The input data from which an inverse-function algorithm should be
constructible. -/
structure InvertibleFunctionOnInterval where
  continuous : ContinuousFunctionOnInterval
  /-- An inverse branch is carried on an actual closed source interval. -/
  source_ordered : continuous.function.lower <= continuous.function.upper
  monotone : MonotoneOnInterval continuous.function
  separation : EffectiveInverseSeparation continuous.function
  /-- The strict separation certificate has the same orientation as the weak
  monotonicity certificate. -/
  orientation :
    match separation.kind with
    | .nondecreasing => monotone.increasing
    | .nonincreasing => ¬ monotone.increasing

namespace InvertibleFunctionOnInterval

def function (I : InvertibleFunctionOnInterval) : FunctionOnInterval :=
  I.continuous.function

end InvertibleFunctionOnInterval

/-! A branch contract for functions whose effective separation depends on the
actual rational input gap. This is the natural interface for exponential,
logarithm, and other functions whose inverse search becomes more precise as
the bracket narrows. It intentionally sits beside the older fixed-gap
contract, so existing inverse certificates remain source-compatible. -/
structure GapAwareInvertibleFunctionOnInterval where
  continuous : ContinuousFunctionOnInterval
  source_ordered : continuous.function.lower <= continuous.function.upper
  monotone : MonotoneOnInterval continuous.function
  separation : GapAwareInverseSeparation continuous.function
  orientation :
    match separation.kind with
    | .nondecreasing => monotone.increasing
    | .nonincreasing => ¬ monotone.increasing

namespace GapAwareInvertibleFunctionOnInterval

def function (I : GapAwareInvertibleFunctionOnInterval) : FunctionOnInterval :=
  I.continuous.function

end GapAwareInvertibleFunctionOnInterval

def GapAwareInvertibleFunctionOnInterval.EndpointRangeContains
    (I : GapAwareInvertibleFunctionOnInterval) (n : Nat) (Y : QInterval) : Prop :=
  match I.separation.kind with
  | .nondecreasing =>
      (I.function.compute I.function.lower
        ⟨Rat.le_refl, I.source_ordered⟩ n).lo <= Y.lo /\
        Y.hi <=
          (I.function.compute I.function.upper
            ⟨I.source_ordered, Rat.le_refl⟩ n).hi
  | .nonincreasing =>
      (I.function.compute I.function.upper
        ⟨I.source_ordered, Rat.le_refl⟩ n).lo <= Y.lo /\
      Y.hi <=
          (I.function.compute I.function.lower
            ⟨Rat.le_refl, I.source_ordered⟩ n).hi

/-! The certified interval image of a rational midpoint, and a sound
interval-level midpoint decision kernel.

The kernel evaluates the degenerate rational midpoint interval.  It only
discards a half when that midpoint image box is wholly on one side of the
target box.  If the boxes overlap, it retains the parent interval instead of
making an unjustified classical choice.  Thus every returned interval is a
rational subinterval of the parent; progress in a full inverse algorithm must
be supplied by a separate gap-aware precision certificate. -/
def gapAwareTargetBisectionMidpointRange
    (F : ContinuousFunctionOnInterval) (I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) :
    QInterval :=
  F.regular.evalInterval
    { lo := I.midpoint, hi := I.midpoint }
    ⟨Rat.le_trans hI.1 (QInterval.midpoint_mem hI.2.1).1,
      Rat.le_refl,
      Rat.le_trans (QInterval.midpoint_mem hI.2.1).2 hI.2.2⟩ n

theorem gapAwareTargetBisectionMidpointRange_ordered
    (F : ContinuousFunctionOnInterval) (I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) :
    (gapAwareTargetBisectionMidpointRange F I hI n).lo <=
      (gapAwareTargetBisectionMidpointRange F I hI n).hi := by
  let M : QInterval := { lo := I.midpoint, hi := I.midpoint }
  have hM : subintervalOf M F.function.lower F.function.upper := by
    exact ⟨Rat.le_trans hI.1 (QInterval.midpoint_mem hI.2.1).1,
      Rat.le_refl,
      Rat.le_trans (QInterval.midpoint_mem hI.2.1).2 hI.2.2⟩
  have hwidth : M.width <=
      1 / ((F.regular.inputPrecision n : Nat) : Rat) := by
    unfold M QInterval.width
    have hp := F.regular.inputPrecision_pos n
    have hden : (0 : Rat) <= (F.regular.inputPrecision n : Nat) := by
      exact Rat.natCast_nonneg
    have hpRat : (0 : Rat) < (F.regular.inputPrecision n : Nat) :=
      (Rat.natCast_pos).2 hp
    have hinv : (0 : Rat) <= ((F.regular.inputPrecision n : Nat) : Rat)⁻¹ :=
      Rat.le_of_lt ((Rat.inv_pos).2 hpRat)
    have hright : (0 : Rat) <=
        1 / ((F.regular.inputPrecision n : Nat) : Rat) := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by decide +kernel) hinv
    rw [Rat.sub_self]
    exact hright
  have hnonneg := (F.regular.output_width M hM n hwidth).1
  change 0 <=
    (F.regular.evalInterval M hM n).hi -
      (F.regular.evalInterval M hM n).lo at hnonneg
  change (F.regular.evalInterval M hM n).lo <=
    (F.regular.evalInterval M hM n).hi
  exact (Rat.le_iff_sub_nonneg _ _).2 hnonneg

def gapAwareTargetBisectionStep
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) :
    QInterval :=
  let V := F.regular.evalInterval
    { lo := I.midpoint, hi := I.midpoint }
    ⟨Rat.le_trans hI.1 (QInterval.midpoint_mem hI.2.1).1,
      Rat.le_refl,
      Rat.le_trans (QInterval.midpoint_mem hI.2.1).2 hI.2.2⟩ n
  if V.hi < Y.lo then
    { lo := I.midpoint, hi := I.hi }
  else if Y.hi < V.lo then
    { lo := I.lo, hi := I.midpoint }
  else
    I

theorem gapAwareTargetBisectionStep_of_below
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat)
    (hbelow :
      (gapAwareTargetBisectionMidpointRange F I hI n).hi < Y.lo) :
    gapAwareTargetBisectionStep F Y I hI n =
      { lo := I.midpoint, hi := I.hi } := by
  have hbelow' :
      (F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 (QInterval.midpoint_mem hI.2.1).1,
          Rat.le_refl,
          Rat.le_trans (QInterval.midpoint_mem hI.2.1).2 hI.2.2⟩ n).hi < Y.lo := by
    simpa [gapAwareTargetBisectionMidpointRange] using hbelow
  simp [gapAwareTargetBisectionStep, hbelow']

theorem gapAwareTargetBisectionStep_of_above
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat)
    (hnotbelow :
      ¬(gapAwareTargetBisectionMidpointRange F I hI n).hi < Y.lo)
    (habove :
      Y.hi < (gapAwareTargetBisectionMidpointRange F I hI n).lo) :
    gapAwareTargetBisectionStep F Y I hI n =
      { lo := I.lo, hi := I.midpoint } := by
  have hnotbelow' :
      ¬(F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 (QInterval.midpoint_mem hI.2.1).1,
          Rat.le_refl,
          Rat.le_trans (QInterval.midpoint_mem hI.2.1).2 hI.2.2⟩ n).hi < Y.lo := by
    simpa [gapAwareTargetBisectionMidpointRange] using hnotbelow
  have habove' :
      Y.hi < (F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 (QInterval.midpoint_mem hI.2.1).1,
          Rat.le_refl,
          Rat.le_trans (QInterval.midpoint_mem hI.2.1).2 hI.2.2⟩ n).lo := by
    simpa [gapAwareTargetBisectionMidpointRange] using habove
  simp [gapAwareTargetBisectionStep, hnotbelow', habove']

def gapAwareTargetBisectionStrictDecision
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) : Prop :=
  (gapAwareTargetBisectionMidpointRange F I hI n).hi < Y.lo \/
    (¬(gapAwareTargetBisectionMidpointRange F I hI n).hi < Y.lo /\
      Y.hi < (gapAwareTargetBisectionMidpointRange F I hI n).lo)

theorem gapAwareTargetBisectionStep_ordered
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) :
    (gapAwareTargetBisectionStep F Y I hI n).lo <=
      (gapAwareTargetBisectionStep F Y I hI n).hi := by
  have hm := QInterval.midpoint_mem hI.2.1
  by_cases hbelow :
      (F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 hm.1, Rat.le_refl,
          Rat.le_trans hm.2 hI.2.2⟩ n).hi < Y.lo
  · simp [gapAwareTargetBisectionStep, hbelow]
    exact hm.2
  · by_cases habove :
        Y.hi < (F.regular.evalInterval
          { lo := I.midpoint, hi := I.midpoint }
          ⟨Rat.le_trans hI.1 hm.1, Rat.le_refl,
            Rat.le_trans hm.2 hI.2.2⟩ n).lo
    · simp [gapAwareTargetBisectionStep, hbelow, habove]
      exact hm.1
    · simp [gapAwareTargetBisectionStep, hbelow, habove]
      exact hI.2.1

theorem gapAwareTargetBisectionStep_subinterval
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) :
    subintervalOf (gapAwareTargetBisectionStep F Y I hI n) I.lo I.hi := by
  have hm := QInterval.midpoint_mem hI.2.1
  by_cases hbelow :
      (F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 hm.1, Rat.le_refl,
          Rat.le_trans hm.2 hI.2.2⟩ n).hi < Y.lo
  · simp [gapAwareTargetBisectionStep, hbelow]
    exact ⟨hm.1, hm.2, Rat.le_refl⟩
  · by_cases habove :
        Y.hi < (F.regular.evalInterval
          { lo := I.midpoint, hi := I.midpoint }
          ⟨Rat.le_trans hI.1 hm.1, Rat.le_refl,
            Rat.le_trans hm.2 hI.2.2⟩ n).lo
    · simp [gapAwareTargetBisectionStep, hbelow, habove]
      exact ⟨Rat.le_refl, hm.1, hm.2⟩
    · simp [gapAwareTargetBisectionStep, hbelow, habove]
      exact ⟨Rat.le_refl, hI.2.1, Rat.le_refl⟩

theorem gapAwareTargetBisectionStep_width_le
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) :
    (gapAwareTargetBisectionStep F Y I hI n).width <= I.width := by
  have hm := QInterval.midpoint_mem hI.2.1
  by_cases hbelow :
      (F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 hm.1, Rat.le_refl,
          Rat.le_trans hm.2 hI.2.2⟩ n).hi < Y.lo
  · simp [gapAwareTargetBisectionStep, hbelow, QInterval.width]
    grind [Rat.sub_eq_add_neg]
  · by_cases habove :
        Y.hi < (F.regular.evalInterval
          { lo := I.midpoint, hi := I.midpoint }
          ⟨Rat.le_trans hI.1 hm.1, Rat.le_refl,
            Rat.le_trans hm.2 hI.2.2⟩ n).lo
    · simp [gapAwareTargetBisectionStep, hbelow, habove, QInterval.width]
      grind [Rat.sub_eq_add_neg]
    · simp [gapAwareTargetBisectionStep, hbelow, habove]

theorem gapAwareTargetBisectionStep_width_eq_half_of_decided
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat)
    (hdecided :
      (F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 (QInterval.midpoint_mem hI.2.1).1,
          Rat.le_refl,
          Rat.le_trans (QInterval.midpoint_mem hI.2.1).2 hI.2.2⟩ n).hi < Y.lo \/
        Y.hi < (F.regular.evalInterval
          { lo := I.midpoint, hi := I.midpoint }
          ⟨Rat.le_trans hI.1 (QInterval.midpoint_mem hI.2.1).1,
            Rat.le_refl,
            Rat.le_trans (QInterval.midpoint_mem hI.2.1).2 hI.2.2⟩ n).lo) :
    (gapAwareTargetBisectionStep F Y I hI n).width = I.width / 2 := by
  have hm := QInterval.midpoint_mem hI.2.1
  by_cases hbelow :
      (F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 hm.1, Rat.le_refl,
          Rat.le_trans hm.2 hI.2.2⟩ n).hi < Y.lo
  · simp only [gapAwareTargetBisectionStep, hbelow, if_pos]
    simpa [QInterval.width, QInterval.midpoint] using
      Integral.midpoint_right_width I.lo I.hi
  · have habove : Y.hi < (F.regular.evalInterval
        { lo := I.midpoint, hi := I.midpoint }
        ⟨Rat.le_trans hI.1 hm.1, Rat.le_refl,
          Rat.le_trans hm.2 hI.2.2⟩ n).lo := by
      rcases hdecided with h | h
      · exact False.elim (hbelow h)
      · exact h
    simp only [gapAwareTargetBisectionStep, hbelow, habove]
    simpa [QInterval.width, QInterval.midpoint] using
      Integral.midpoint_left_width I.lo I.hi

theorem gapAwareTargetBisectionStep_congr
    (F : ContinuousFunctionOnInterval) (Y : QInterval)
    {I J : QInterval}
    (hI : subintervalOf I F.function.lower F.function.upper)
    (hJ : subintervalOf J F.function.lower F.function.upper)
    (hIJ : I = J) (n : Nat) :
    gapAwareTargetBisectionStep F Y I hI n =
      gapAwareTargetBisectionStep F Y J hJ n := by
  subst J
  rfl

/-! Proof-carrying finite iteration of the conservative kernel.  The subtype
stores the domain certificate at every stage, so later clients never need to
reconstruct that a midpoint refinement stayed inside the original branch. -/
def gapAwareTargetBisectionIterateWithProof
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) :
    Nat -> {J : QInterval // subintervalOf J F.function.lower F.function.upper}
  | 0 => ⟨I, hI⟩
  | n + 1 =>
      let P := gapAwareTargetBisectionIterateWithProof F Y I hI n
      let J := gapAwareTargetBisectionStep F Y P.1 P.2 n
      have hstep := gapAwareTargetBisectionStep_subinterval F Y P.1 P.2 n
      ⟨J, ⟨Rat.le_trans P.2.1 hstep.1, hstep.2.1,
        Rat.le_trans hstep.2.2 P.2.2.2⟩⟩

def gapAwareTargetBisectionIterate
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) : QInterval :=
  (gapAwareTargetBisectionIterateWithProof F Y I hI n).1

theorem gapAwareTargetBisectionIterate_subinterval
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) :
    subintervalOf (gapAwareTargetBisectionIterate F Y I hI n)
      F.function.lower F.function.upper :=
  (gapAwareTargetBisectionIterateWithProof F Y I hI n).2

theorem gapAwareTargetBisectionIterate_width_le
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper) (n : Nat) :
    (gapAwareTargetBisectionIterate F Y I hI n).width <= I.width := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
      let P := gapAwareTargetBisectionIterateWithProof F Y I hI n
      have hstep := gapAwareTargetBisectionStep_width_le F Y P.1 P.2 n
      have hprev : P.1.width <= I.width := ih
      exact Rat.le_trans hstep hprev

/-! A fixed-precision variant is useful for executable traces: the evaluator
precision is held constant while the source bracket is refined.  This is
distinct from the stage-indexed iterator above, whose precision may grow with
the requested output stage. -/
def gapAwareTargetBisectionFixedIterateWithProof
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat) :
    Nat -> {J : QInterval // subintervalOf J F.function.lower F.function.upper}
  | 0 => ⟨I, hI⟩
  | n + 1 =>
      let P := gapAwareTargetBisectionFixedIterateWithProof F Y I hI precision n
      let J := gapAwareTargetBisectionStep F Y P.1 P.2 precision
      have hstep := gapAwareTargetBisectionStep_subinterval F Y P.1 P.2 precision
      ⟨J, ⟨Rat.le_trans P.2.1 hstep.1, hstep.2.1,
        Rat.le_trans hstep.2.2 P.2.2.2⟩⟩

def gapAwareTargetBisectionFixedIterate
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision n : Nat) : QInterval :=
  (gapAwareTargetBisectionFixedIterateWithProof F Y I hI precision n).1

theorem gapAwareTargetBisectionFixedIterate_subinterval
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision n : Nat) :
    subintervalOf (gapAwareTargetBisectionFixedIterate F Y I hI precision n)
      F.function.lower F.function.upper :=
  (gapAwareTargetBisectionFixedIterateWithProof F Y I hI precision n).2

theorem gapAwareTargetBisectionFixedIterate_width_le
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision n : Nat) :
    (gapAwareTargetBisectionFixedIterate F Y I hI precision n).width <= I.width := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
      let P := gapAwareTargetBisectionFixedIterateWithProof
        F Y I hI precision n
      have hstep := gapAwareTargetBisectionStep_width_le F Y P.1 P.2 precision
      exact Rat.le_trans hstep ih

/-! A scheduled variant separates the evaluator precision from the number of
midpoint steps.  This is essential for computable inverse branches whose
separation budget grows at a different rate than the requested bracket depth.
The fixed-precision iterator above is retained as its constant-schedule case. -/
def gapAwareTargetBisectionScheduledIterateWithProof
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) :
    Nat -> {J : QInterval // subintervalOf J F.function.lower F.function.upper}
  | 0 => ⟨I, hI⟩
  | n + 1 =>
      let P := gapAwareTargetBisectionScheduledIterateWithProof
        F Y I hI precision n
      let J := gapAwareTargetBisectionStep F Y P.1 P.2 (precision n)
      have hstep := gapAwareTargetBisectionStep_subinterval F Y P.1 P.2
        (precision n)
      ⟨J, ⟨Rat.le_trans P.2.1 hstep.1, hstep.2.1,
        Rat.le_trans hstep.2.2 P.2.2.2⟩⟩

def gapAwareTargetBisectionScheduledIterate
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) (n : Nat) : QInterval :=
  (gapAwareTargetBisectionScheduledIterateWithProof F Y I hI precision n).1

theorem gapAwareTargetBisectionScheduledIterate_subinterval
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) (n : Nat) :
    subintervalOf (gapAwareTargetBisectionScheduledIterate F Y I hI precision n)
      F.function.lower F.function.upper :=
  (gapAwareTargetBisectionScheduledIterateWithProof F Y I hI precision n).2

theorem gapAwareTargetBisectionScheduledIterate_width_le
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) (n : Nat) :
    (gapAwareTargetBisectionScheduledIterate F Y I hI precision n).width <=
      I.width := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
      let P := gapAwareTargetBisectionScheduledIterateWithProof
        F Y I hI precision n
      have hstep := gapAwareTargetBisectionStep_width_le F Y P.1 P.2
        (precision n)
      exact Rat.le_trans hstep ih

def gapAwareTargetBisectionScheduledDecision
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) (n : Nat) : Prop :=
  let P := gapAwareTargetBisectionScheduledIterateWithProof
    F Y I hI precision n
  (F.regular.evalInterval
      { lo := P.1.midpoint, hi := P.1.midpoint }
      ⟨Rat.le_trans P.2.1 (QInterval.midpoint_mem P.2.2.1).1,
        Rat.le_refl,
        Rat.le_trans (QInterval.midpoint_mem P.2.2.1).2 P.2.2.2⟩
      (precision n)).hi < Y.lo \/
    Y.hi <
      (F.regular.evalInterval
        { lo := P.1.midpoint, hi := P.1.midpoint }
        ⟨Rat.le_trans P.2.1 (QInterval.midpoint_mem P.2.2.1).1,
          Rat.le_refl,
          Rat.le_trans (QInterval.midpoint_mem P.2.2.1).2 P.2.2.2⟩
        (precision n)).lo

theorem gapAwareTargetBisectionScheduledIterate_width_eq_div_pow_of_decided
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) (n : Nat)
    (hdecided : forall k, k < n ->
      gapAwareTargetBisectionScheduledDecision F Y I hI precision k) :
    (gapAwareTargetBisectionScheduledIterate F Y I hI precision n).width =
      I.width / (2 ^ n : Rat) := by
  induction n with
  | zero =>
      simp [gapAwareTargetBisectionScheduledIterate,
        gapAwareTargetBisectionScheduledIterateWithProof, QInterval.width,
        Rat.div_def]
      have hone : (1 : Rat)⁻¹ = 1 := by
        have h := Rat.mul_inv_cancel (1 : Rat) (by decide +kernel)
        simpa using h
      rw [hone, Rat.mul_one]
  | succ n ih =>
      let P := gapAwareTargetBisectionScheduledIterateWithProof
        F Y I hI precision n
      have hstep := gapAwareTargetBisectionStep_width_eq_half_of_decided
        F Y P.1 P.2 (precision n) (by
          simpa [gapAwareTargetBisectionScheduledDecision, P] using
            hdecided n (by omega))
      have hprev : P.1.width = I.width / (2 ^ n : Rat) := by
        change
          (gapAwareTargetBisectionScheduledIterate F Y I hI precision n).width =
            I.width / (2 ^ n : Rat)
        apply ih
        intro k hk
        exact hdecided k (by omega)
      change
        (gapAwareTargetBisectionStep F Y P.1 P.2 (precision n)).width =
          I.width / (2 ^ (n + 1) : Rat)
      rw [hstep, hprev, Rat.pow_succ]
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem gapAwareTargetBisectionScheduledIterate_width_eq_div_pow_of_strictly_decided
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) (n : Nat)
    (hdecided : forall k, k < n ->
      gapAwareTargetBisectionStrictDecision F Y
        (gapAwareTargetBisectionScheduledIterate F Y I hI precision k)
        (gapAwareTargetBisectionScheduledIterate_subinterval F Y I hI precision k)
        (precision k)) :
    (gapAwareTargetBisectionScheduledIterate F Y I hI precision n).width =
      I.width / (2 ^ n : Rat) := by
  apply gapAwareTargetBisectionScheduledIterate_width_eq_div_pow_of_decided
  intro k hk
  have h := hdecided k hk
  let P := gapAwareTargetBisectionScheduledIterateWithProof F Y I hI
    precision k
  change gapAwareTargetBisectionStrictDecision F Y P.1 P.2
    (precision k) at h
  rcases h with hbelow | ⟨_, habove⟩
  · left
    simpa [gapAwareTargetBisectionMidpointRange] using hbelow
  · right
    simpa [gapAwareTargetBisectionMidpointRange] using habove

theorem gapAwareTargetBisectionScheduledIterate_mem_of_oriented
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) {r : Rat} (hrI : I.lo <= r /\ r <= I.hi)
    (n : Nat)
    (horiented : forall j, j < n ->
      let P := gapAwareTargetBisectionScheduledIterateWithProof
        F Y I hI precision j
      ((P.1.midpoint < r /\
          (gapAwareTargetBisectionMidpointRange F P.1 P.2
            (precision j)).hi < Y.lo) \/
        (r < P.1.midpoint /\
          ¬(gapAwareTargetBisectionMidpointRange F P.1 P.2
            (precision j)).hi < Y.lo /\
          Y.hi < (gapAwareTargetBisectionMidpointRange F P.1 P.2
            (precision j)).lo))) :
    (gapAwareTargetBisectionScheduledIterate F Y I hI precision n).lo <= r /\
      r <= (gapAwareTargetBisectionScheduledIterate F Y I hI precision n).hi := by
  induction n with
  | zero =>
      simpa [gapAwareTargetBisectionScheduledIterate,
        gapAwareTargetBisectionScheduledIterateWithProof] using hrI
  | succ n ih =>
      let P := gapAwareTargetBisectionScheduledIterateWithProof
        F Y I hI precision n
      have hprev := ih (fun j hj => horiented j (by omega))
      have hdir := horiented n (by omega)
      change
        ((P.1.midpoint < r /\
            (gapAwareTargetBisectionMidpointRange F P.1 P.2
              (precision n)).hi < Y.lo) \/
          (r < P.1.midpoint /\
            ¬(gapAwareTargetBisectionMidpointRange F P.1 P.2
              (precision n)).hi < Y.lo /\
            Y.hi < (gapAwareTargetBisectionMidpointRange F P.1 P.2
              (precision n)).lo)) at hdir
      change
        (gapAwareTargetBisectionStep F Y P.1 P.2 (precision n)).lo <= r /\
          r <= (gapAwareTargetBisectionStep F Y P.1 P.2
            (precision n)).hi
      rcases hdir with ⟨hmr, hbelow⟩ | ⟨hrm, hnotbelow, habove⟩
      · rw [gapAwareTargetBisectionStep_of_below F Y P.1 P.2
          (precision n) hbelow]
        exact ⟨Rat.le_of_lt hmr, hprev.2⟩
      · rw [gapAwareTargetBisectionStep_of_above F Y P.1 P.2
          (precision n) hnotbelow habove]
        exact ⟨hprev.1, Rat.le_of_lt hrm⟩

theorem gapAwareTargetBisectionScheduledIterate_nested
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) {n m : Nat} (hnm : n ≤ m) :
    (gapAwareTargetBisectionScheduledIterate F Y I hI precision n).lo ≤
        (gapAwareTargetBisectionScheduledIterate F Y I hI precision m).lo /\
      (gapAwareTargetBisectionScheduledIterate F Y I hI precision m).lo ≤
        (gapAwareTargetBisectionScheduledIterate F Y I hI precision m).hi /\
      (gapAwareTargetBisectionScheduledIterate F Y I hI precision m).hi ≤
        (gapAwareTargetBisectionScheduledIterate F Y I hI precision n).hi := by
  induction hnm with
  | refl =>
      have hsub := gapAwareTargetBisectionScheduledIterate_subinterval
        F Y I hI precision n
      exact ⟨Rat.le_refl, hsub.2.1, Rat.le_refl⟩
  | @step m hnm ih =>
      have hprev := ih
      have hstep := gapAwareTargetBisectionStep_subinterval F Y
        (gapAwareTargetBisectionScheduledIterate F Y I hI precision m)
        (gapAwareTargetBisectionScheduledIterate_subinterval F Y I hI precision m)
        (precision m)
      have hcurrent := gapAwareTargetBisectionScheduledIterate_subinterval
        F Y I hI precision m
      have hJ := gapAwareTargetBisectionScheduledIterate_subinterval
        F Y I hI precision (m + 1)
      exact ⟨Rat.le_trans hprev.1 hstep.1,
        hJ.2.1,
        Rat.le_trans hstep.2.2 hprev.2.2⟩

/-! The fully gap-aware form may choose precision from the current bracket as
well as the step index.  This is the form needed when a separation modulus is
computed from the actual midpoint gap. -/
def gapAwareTargetBisectionAdaptiveIterateWithProof
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> QInterval -> Nat) :
    Nat -> {J : QInterval // subintervalOf J F.function.lower F.function.upper}
  | 0 => ⟨I, hI⟩
  | n + 1 =>
      let P := gapAwareTargetBisectionAdaptiveIterateWithProof
        F Y I hI precision n
      let J := gapAwareTargetBisectionStep F Y P.1 P.2
        (precision n P.1)
      have hstep := gapAwareTargetBisectionStep_subinterval F Y P.1 P.2
        (precision n P.1)
      ⟨J, ⟨Rat.le_trans P.2.1 hstep.1, hstep.2.1,
        Rat.le_trans hstep.2.2 P.2.2.2⟩⟩

def gapAwareTargetBisectionAdaptiveIterate
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> QInterval -> Nat) (n : Nat) : QInterval :=
  (gapAwareTargetBisectionAdaptiveIterateWithProof F Y I hI precision n).1

/-! If the adaptive precision choice ignores the current bracket, the adaptive
iterator is exactly the scheduled iterator.  This is the bridge used by
concrete inverse branches: a target-specific stage schedule can be proved
once, then supplied to the fully bracket-aware interface without duplicating
the bisection argument. -/
theorem gapAwareTargetBisectionAdaptiveIterate_eq_scheduled
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> Nat) (n : Nat) :
    gapAwareTargetBisectionAdaptiveIterate F Y I hI
        (fun k _ => precision k) n =
      gapAwareTargetBisectionScheduledIterate F Y I hI precision n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [gapAwareTargetBisectionAdaptiveIterate,
        gapAwareTargetBisectionAdaptiveIterateWithProof,
        gapAwareTargetBisectionScheduledIterate,
        gapAwareTargetBisectionScheduledIterateWithProof]
      have hP :
          (gapAwareTargetBisectionAdaptiveIterateWithProof F Y I hI
            (fun k _ => precision k) n).1 =
            (gapAwareTargetBisectionScheduledIterateWithProof F Y I hI
              precision n).1 := by
        simpa [gapAwareTargetBisectionAdaptiveIterate,
          gapAwareTargetBisectionScheduledIterate] using ih
      exact gapAwareTargetBisectionStep_congr F Y _ _ hP (precision n)

theorem gapAwareTargetBisectionAdaptiveIterate_subinterval
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> QInterval -> Nat) (n : Nat) :
    subintervalOf (gapAwareTargetBisectionAdaptiveIterate F Y I hI precision n)
      F.function.lower F.function.upper :=
  (gapAwareTargetBisectionAdaptiveIterateWithProof F Y I hI precision n).2

theorem gapAwareTargetBisectionAdaptiveIterate_width_le
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> QInterval -> Nat) (n : Nat) :
    (gapAwareTargetBisectionAdaptiveIterate F Y I hI precision n).width <=
      I.width := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
      let P := gapAwareTargetBisectionAdaptiveIterateWithProof
        F Y I hI precision n
      have hstep := gapAwareTargetBisectionStep_width_le F Y P.1 P.2
        (precision n P.1)
      exact Rat.le_trans hstep ih

def gapAwareTargetBisectionAdaptiveDecision
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> QInterval -> Nat) (n : Nat) : Prop :=
  let P := gapAwareTargetBisectionAdaptiveIterateWithProof
    F Y I hI precision n
  (F.regular.evalInterval
      { lo := P.1.midpoint, hi := P.1.midpoint }
      ⟨Rat.le_trans P.2.1 (QInterval.midpoint_mem P.2.2.1).1,
        Rat.le_refl,
        Rat.le_trans (QInterval.midpoint_mem P.2.2.1).2 P.2.2.2⟩
      (precision n P.1)).hi < Y.lo \/
    Y.hi <
      (F.regular.evalInterval
        { lo := P.1.midpoint, hi := P.1.midpoint }
        ⟨Rat.le_trans P.2.1 (QInterval.midpoint_mem P.2.2.1).1,
          Rat.le_refl,
          Rat.le_trans (QInterval.midpoint_mem P.2.2.1).2 P.2.2.2⟩
        (precision n P.1)).lo

theorem gapAwareTargetBisectionAdaptiveIterate_width_eq_div_pow_of_decided
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision : Nat -> QInterval -> Nat) (n : Nat)
    (hdecided : forall k, k < n ->
      gapAwareTargetBisectionAdaptiveDecision F Y I hI precision k) :
    (gapAwareTargetBisectionAdaptiveIterate F Y I hI precision n).width =
      I.width / (2 ^ n : Rat) := by
  induction n with
  | zero =>
      simp [gapAwareTargetBisectionAdaptiveIterate,
        gapAwareTargetBisectionAdaptiveIterateWithProof, QInterval.width,
        Rat.div_def]
      have hone : (1 : Rat)⁻¹ = 1 := by
        have h := Rat.mul_inv_cancel (1 : Rat) (by decide +kernel)
        simpa using h
      rw [hone, Rat.mul_one]
  | succ n ih =>
      let P := gapAwareTargetBisectionAdaptiveIterateWithProof
        F Y I hI precision n
      have hstep := gapAwareTargetBisectionStep_width_eq_half_of_decided
        F Y P.1 P.2 (precision n P.1) (by
          simpa [gapAwareTargetBisectionAdaptiveDecision, P] using
            hdecided n (by omega))
      have hprev : P.1.width = I.width / (2 ^ n : Rat) := by
        change
          (gapAwareTargetBisectionAdaptiveIterate F Y I hI precision n).width =
            I.width / (2 ^ n : Rat)
        apply ih
        intro k hk
        exact hdecided k (by omega)
      change
        (gapAwareTargetBisectionStep F Y P.1 P.2
          (precision n P.1)).width =
          I.width / (2 ^ (n + 1) : Rat)
      rw [hstep, hprev, Rat.pow_succ]
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

def gapAwareTargetBisectionFixedDecision
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision n : Nat) : Prop :=
  let P := gapAwareTargetBisectionFixedIterateWithProof
    F Y I hI precision n
  (F.regular.evalInterval
      { lo := P.1.midpoint, hi := P.1.midpoint }
      ⟨Rat.le_trans P.2.1 (QInterval.midpoint_mem P.2.2.1).1,
        Rat.le_refl,
        Rat.le_trans (QInterval.midpoint_mem P.2.2.1).2 P.2.2.2⟩ precision).hi < Y.lo \/
    Y.hi <
      (F.regular.evalInterval
        { lo := P.1.midpoint, hi := P.1.midpoint }
        ⟨Rat.le_trans P.2.1 (QInterval.midpoint_mem P.2.2.1).1,
          Rat.le_refl,
          Rat.le_trans (QInterval.midpoint_mem P.2.2.1).2 P.2.2.2⟩ precision).lo

theorem gapAwareTargetBisectionFixedIterate_width_eq_div_pow_of_decided
    (F : ContinuousFunctionOnInterval) (Y I : QInterval)
    (hI : subintervalOf I F.function.lower F.function.upper)
    (precision n : Nat)
    (hdecided : forall k, k < n ->
      gapAwareTargetBisectionFixedDecision F Y I hI precision k) :
    (gapAwareTargetBisectionFixedIterate F Y I hI precision n).width =
      I.width / (2 ^ n : Rat) := by
  induction n with
  | zero =>
      simp [gapAwareTargetBisectionFixedIterate,
        gapAwareTargetBisectionFixedIterateWithProof, QInterval.width,
        Rat.div_def]
      have hone : (1 : Rat)⁻¹ = 1 := by
        have h := Rat.mul_inv_cancel (1 : Rat) (by decide +kernel)
        simpa using h
      rw [hone, Rat.mul_one]
  | succ n ih =>
      let P := gapAwareTargetBisectionFixedIterateWithProof
        F Y I hI precision n
      have hstep := gapAwareTargetBisectionStep_width_eq_half_of_decided
        F Y P.1 P.2 precision (hdecided n (by omega))
      have hprev : P.1.width = I.width / (2 ^ n : Rat) := by
        change (gapAwareTargetBisectionFixedIterate F Y I hI precision n).width =
          I.width / (2 ^ n : Rat)
        apply ih
        intro k hk
        exact hdecided k (by omega)
      change (gapAwareTargetBisectionStep F Y P.1 P.2 precision).width =
        I.width / (2 ^ (n + 1) : Rat)
      rw [hstep, hprev, Rat.pow_succ]
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

structure GapAwareInRangeRaw
    (I : GapAwareInvertibleFunctionOnInterval) where
  value : RealCompute
  value_valid : value.Valid
  rangePrecision : Nat -> Nat
  in_range : forall n,
    I.EndpointRangeContains (rangePrecision n) (value.compute n)

structure GapAwareInverseBisectionSearch
    (I : GapAwareInvertibleFunctionOnInterval)
    (y : GapAwareInRangeRaw I) where
  compute_preimage : Nat -> QInterval
  valid_preimage : RealCompute.ValidCompute compute_preimage
  preimage_subinterval :
    forall n, subintervalOf (compute_preimage n)
      I.function.lower I.function.upper
  value_overlaps :
    forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (compute_preimage n)
          (preimage_subinterval n)
          n)
        (y.value.compute n)

structure GapAwareInverseRaw
    (I : GapAwareInvertibleFunctionOnInterval) where
  compute_preimage : GapAwareInRangeRaw I -> Nat -> QInterval
  valid_preimage : forall y, RealCompute.ValidCompute (compute_preimage y)
  preimage_subinterval : forall y n,
    subintervalOf (compute_preimage y n)
      I.function.lower I.function.upper
  value_overlaps : forall y n,
    QInterval.Overlaps
      (I.continuous.regular.evalInterval
        (compute_preimage y n)
        (preimage_subinterval y n) n)
      (y.value.compute n)

def gapAwareInverseRawOfSearch
    {I : GapAwareInvertibleFunctionOnInterval}
    (search : forall y : GapAwareInRangeRaw I,
      GapAwareInverseBisectionSearch I y) : GapAwareInverseRaw I where
  compute_preimage := fun y => (search y).compute_preimage
  valid_preimage := fun y => (search y).valid_preimage
  preimage_subinterval := fun y => (search y).preimage_subinterval
  value_overlaps := fun y => (search y).value_overlaps

def GapAwareHasBisectionSearch
    (I : GapAwareInvertibleFunctionOnInterval) :=
  forall y : GapAwareInRangeRaw I,
    GapAwareInverseBisectionSearch I y

theorem gapAwareInverseRaw_of_search
    {I : GapAwareInvertibleFunctionOnInterval}
    (hsearch : GapAwareHasBisectionSearch I) :
    Nonempty (GapAwareInverseRaw I) :=
  ⟨gapAwareInverseRawOfSearch hsearch⟩

/-- The endpoint-value box at the lower end of an invertible interval branch. -/
def InvertibleFunctionOnInterval.lowerValueBox
    (I : InvertibleFunctionOnInterval) (n : Nat) : QInterval :=
  I.function.compute I.function.lower
    ⟨Rat.le_refl, I.source_ordered⟩ n

/-- The endpoint-value box at the upper end of an invertible interval branch. -/
def InvertibleFunctionOnInterval.upperValueBox
    (I : InvertibleFunctionOnInterval) (n : Nat) : QInterval :=
  I.function.compute I.function.upper
    ⟨I.source_ordered, Rat.le_refl⟩ n

/-- An interval box lies in the oriented endpoint range of an invertible
branch.  The endpoint precision is explicit because a target algorithm and a
forward evaluator need not use the same stage schedule. -/
def InvertibleFunctionOnInterval.EndpointRangeContains
    (I : InvertibleFunctionOnInterval) (n : Nat) (Y : QInterval) : Prop :=
  match I.separation.kind with
  | .nondecreasing =>
      (I.lowerValueBox n).lo <= Y.lo /\
        Y.hi <= (I.upperValueBox n).hi
  | .nonincreasing =>
      (I.upperValueBox n).lo <= Y.lo /\
        Y.hi <= (I.lowerValueBox n).hi

/-- A computable target value in the range of an interval function.

The target carries its own raw-real validity certificate and an explicit
endpoint-range enclosure at every target stage.  This is the finite data a
bisection implementation may inspect; a bare proposition saying that a value
is ``in range'' would not support a constructive inverse search. -/
structure InRangeRaw (I : InvertibleFunctionOnInterval) where
  value : RealCompute
  value_valid : value.Valid
  rangePrecision : Nat -> Nat
  in_range : forall n,
    I.EndpointRangeContains (rangePrecision n) (value.compute n)

/-- A raw inverse evaluator on computable real target values.

It is partial because the inverse is only defined on the certified output
range.  The `compute_preimage` field returns a rational interval in the
original domain containing an input whose function value matches the output
target at the requested scale. -/
structure InverseRaw (I : InvertibleFunctionOnInterval) where
  compute_preimage : InRangeRaw I -> Nat -> QInterval
  valid_preimage : forall y, RealCompute.ValidCompute (compute_preimage y)
  preimage_subinterval : forall y n,
    subintervalOf (compute_preimage y n) I.function.lower I.function.upper
  value_overlaps :
    forall y n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (compute_preimage y n)
          (preimage_subinterval y n)
          n)
        (y.value.compute n)

namespace InverseRaw

def apply {I : InvertibleFunctionOnInterval} (inv : InverseRaw I) (y : InRangeRaw I) :
    RealCompute where
  compute := inv.compute_preimage y

theorem apply_valid {I : InvertibleFunctionOnInterval} (inv : InverseRaw I)
    (y : InRangeRaw I) :
    RealCompute.Valid (inv.apply y) :=
  inv.valid_preimage y

theorem apply_stays_in_source {I : InvertibleFunctionOnInterval}
    (inv : InverseRaw I) (y : InRangeRaw I) :
    forall n, subintervalOf ((inv.apply y).compute n) I.function.lower I.function.upper :=
  inv.preimage_subinterval y

/-! A rational preimage certificate upgrades an inverse interval computation
from mere source validity to an explicit represented value.  This is the
small inverse-layer fact needed by half-angle constructions: the geometric
argument supplies a rational slope `u`, while this theorem supplies its
`RealCompute.Equiv` statement. -/
theorem apply_equiv_of_rational_preimage
    {I : InvertibleFunctionOnInterval} (inv : InverseRaw I)
    (y : InRangeRaw I) (u : Rat)
    (hpreimage : forall n,
      QInterval.Overlaps
        ((inv.apply y).compute n)
        ({ lo := u, hi := u } : QInterval)) :
    (inv.apply y).Equiv (RealCompute.ofRat u) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (inv.apply y) (RealCompute.ofRat u) n n).2
  simpa [RealCompute.ofRat] using hpreimage n

theorem apply_value_overlaps_target {I : InvertibleFunctionOnInterval}
    (inv : InverseRaw I) (y : InRangeRaw I) :
    forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          ((inv.apply y).compute n)
          (apply_stays_in_source inv y n)
          n)
        (y.value.compute n) :=
  inv.value_overlaps y

end InverseRaw

/-- A particular monotone interval branch has a constructive inverse when its
certified output range admits a raw preimage evaluator.  This is deliberately
branch-local: an inverse is only meaningful after its source interval,
orientation, and range certificate have been fixed. -/
def HasInverse (I : InvertibleFunctionOnInterval) : Prop :=
  Nonempty (InverseRaw I)

/-- The remaining algorithmic step for the inverse function theorem:
construct the inverse intervals by bisection/search. -/
structure InverseBisectionSearch (I : InvertibleFunctionOnInterval) (y : InRangeRaw I) where
  compute_preimage : Nat -> QInterval
  valid_preimage : RealCompute.ValidCompute compute_preimage
  preimage_subinterval :
    forall n, subintervalOf (compute_preimage n) I.function.lower I.function.upper
  value_overlaps :
    forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (compute_preimage n)
          (preimage_subinterval n)
          n)
        (y.value.compute n)

/-- Computational data assigning a finite certified search to every target in
the stated range.  This is data, rather than a merely nonempty proposition,
so assembling the inverse does not invoke a choice principle. -/
def HasBisectionSearch (I : InvertibleFunctionOnInterval) :=
  forall y : InRangeRaw I, InverseBisectionSearch I y

def inverseRawOfSearch {I : InvertibleFunctionOnInterval}
    (search : forall y : InRangeRaw I, InverseBisectionSearch I y) :
    InverseRaw I where
  compute_preimage := fun y => (search y).compute_preimage
  valid_preimage := fun y => (search y).valid_preimage
  preimage_subinterval := fun y => (search y).preimage_subinterval
  value_overlaps := fun y => (search y).value_overlaps

theorem inverse_function_from_bisection_search
    {I : InvertibleFunctionOnInterval}
    (hsearch : HasBisectionSearch I) :
    HasInverse I := by
  exact ⟨inverseRawOfSearch hsearch⟩
end ComputableAnalysis

namespace ComputableAnalysis
theorem precisionAtStage_shrinksToZero :
    ShrinksToZero (fun n => (precisionAtStage n).val) := by
  intro eps
  let N : Nat := eps.val.den + 1
  refine ⟨N, ?_⟩
  intro n hn
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hnpos : 0 < n := Nat.lt_of_lt_of_le hNpos hn
  have hmono : (1 / (n : Rat)) <= 1 / (N : Rat) := by
    have hNrat : (0 : Rat) < (N : Rat) := (Rat.natCast_pos).2 hNpos
    have hnrat : (0 : Rat) < (n : Rat) := (Rat.natCast_pos).2 hnpos
    have hNne : (N : Rat) ≠ 0 := Rat.ne_of_gt hNrat
    have hnne : (n : Rat) ≠ 0 := Rat.ne_of_gt hnrat
    apply Rat.le_of_mul_le_mul_right (c := (N : Rat) * (n : Rat))
    · calc
        (1 / (n : Rat)) * ((N : Rat) * (n : Rat)) = (N : Rat) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= (n : Rat) := by exact_mod_cast hn
        _ = (1 / (N : Rat)) * ((N : Rat) * (n : Rat)) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact Rat.mul_pos hNrat hnrat
  calc
    (precisionAtStage n).val = 1 / (n : Rat) := by
      simp [precisionAtStage, Nat.ne_of_gt hnpos]
    _ <= 1 / (N : Rat) := hmono
    _ = 1 / (((eps.val.den + 1 : Nat) : Rat)) := by rfl
    _ <= eps.val := one_div_den_succ_le_of_pos eps.property


namespace DerivativeBoundFTC
theorem boundedIntegralRaw_width_le_of_tolerance
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) (n : Nat) :
    (h.boundedIntegralRaw.compute n).width <= (precisionAtStage n).val := by
  exact h.riemann_width (precisionAtStage n)

theorem boundedIntegralRaw_widths_shrink
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) :
    RealCompute.WidthsShrinkToZero h.boundedIntegralRaw.compute := by
  intro eps
  obtain ⟨N, hN⟩ := precisionAtStage_shrinksToZero eps
  refine ⟨N, ?_⟩
  intro n hn
  exact Rat.le_trans
    (h.boundedIntegralRaw_width_le_of_tolerance n)
    (hN n hn)


end DerivativeBoundFTC
def EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    RealCompute :=
  RealCompute.prefixStabilize h.toDerivativeBoundFTC.boundedIntegralRaw
    (fun n =>
      ((endpointDifferenceRaw F a b hendpoint).compute n).width)

theorem EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_width_le
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    (n : Nat) :
    ((h.stabilizedBoundedIntegralRaw hendpoint).compute n).width <=
      (h.toDerivativeBoundFTC.boundedIntegralRaw.compute n).width +
        2 * ((endpointDifferenceRaw F a b hendpoint).compute n).width := by
  exact RealCompute.prefixStabilize_width_le_current_expand
    h.toDerivativeBoundFTC.boundedIntegralRaw
    (fun n =>
      ((endpointDifferenceRaw F a b hendpoint).compute n).width) n

theorem EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_valid
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    (h.stabilizedBoundedIntegralRaw hendpoint).Valid := by
  unfold EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw
  apply RealCompute.prefixStabilize_valid
    h.toDerivativeBoundFTC.boundedIntegralRaw_widths_shrink
    (by simpa [endpointDifferenceRaw, RealCompute.Valid] using hendpoint)
    (h.boundedIntegralRaw_equiv_endpointDifference hendpoint)
  · intro n
    exact Rat.le_refl
  · exact hendpoint.2.2

theorem EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    (h.stabilizedBoundedIntegralRaw hendpoint).Equiv
      (endpointDifferenceRaw F a b hendpoint) := by
  unfold EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw
  apply RealCompute.prefixStabilize_equiv_anchor
    (by simpa [endpointDifferenceRaw, RealCompute.Valid] using hendpoint)
    (h.boundedIntegralRaw_equiv_endpointDifference hendpoint)
  intro n
  exact Rat.le_refl


namespace FunctionOnInterval
def ofRealFunRaw
    (f : RealFunRaw) (a b : Rat)
    (hdomain : forall x, inDomainInterval a b x -> f.domain x)
    (hvalid : f.Valid) : FunctionOnInterval where
  raw :=
    { definedAt := inDomainInterval a b
      compute := fun x _hx n => f.compute x n
      rate := fun x hx => f.rate x (hdomain x hx) }
  lower := a
  upper := b
  defined_on := fun _x hx => hx
  valid_on := fun x hx => hvalid x (hdomain x hx)


end FunctionOnInterval

namespace Integral
def effectiveFTCCandidateConstructionFor
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hdF : dF.Valid)
    (hdomain : forall x, inDomainInterval a b x -> dF.domain x)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    CandidateConstructionFor (FunctionOnInterval.ofRealFunRaw dF a b hdomain hdF) where
  compute := (h.stabilizedBoundedIntegralRaw hendpoint).compute
  certificate := h.stabilizedBoundedIntegralRaw_valid hendpoint

/-- User-facing effective FTC: the domain-aware constructed integral equals
the primitive endpoint difference. -/
theorem effectiveFTCIntegral_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hdF : dF.Valid)
    (hdomain : forall x, inDomainInterval a b x -> dF.domain x)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b)) :
    (candidateValueFor (FunctionOnInterval.ofRealFunRaw dF a b hdomain hdF)
      (effectiveFTCCandidateConstructionFor
        h hdF hdomain hendpoint)).Equiv
      (endpointDifferenceRaw F a b hendpoint) := by
  exact h.stabilizedBoundedIntegralRaw_equiv_endpointDifference hendpoint


end Integral
end ComputableAnalysis


