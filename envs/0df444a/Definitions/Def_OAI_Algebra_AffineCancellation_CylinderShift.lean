-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
-- name    : OAI_Algebra_AffineCancellation_CylinderShift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:47:40.198163+00:00
-- url     : https://prove2.me/theorems/43175d80-f4bd-4259-a028-37f735127813
-- title:
--   Additive shift action and linear frame coordinates for the hypersurface $x^2f-(1+2sx)j-p^2j^2-pu=0$
-- statement:
--   Throughout, $R$ is an arbitrary commutative ring. This file sets up explicit polynomial maps on quintuples and quadruples of elements of $R$. They will later identify the cylinder over the hypersurface below with affine space, and none of them divides by the distinguished coordinate $p$.
--
--   1. **Points and the equation.** A point is a quintuple $q=(p,s,u,f,j)\in R^5$. Put
--   $$x(q)=s^2+u^3+p^2f,\qquad E(q)=x^2f-(1+2sx)\,j-p^2j^2-pu .$$
--   For the five variables of $\mathbb{C}[p,s,u,F,J]$ this is the polynomial $H=x^2F-(1+2sx)J-p^2J^2-pu$ with $x=s^2+u^3+p^2F$.
--
--   2. **Cubic difference.** For $p,u,w\in R$ let $\delta(p,u,w)=-3u^2w+3up^2w^2-p^4w^3$. It satisfies $(u-p^2w)^3=u^3+p^2\,\delta(p,u,w)$ and the cocycle rule $\delta(p,u,w)+\delta(p,u-p^2w,z)=\delta(p,u,w+z)$ for all $z\in R$.
--
--   3. **Shift.** For a point $q$, an element $w\in R$ and $k=\delta(p,u,w)$, set
--   $$\sigma_w(p,s,u,f,j)=\bigl(p,\ s+p^2xk,\ u-p^2w,\ f-(2sx+1)k-p^2x^2k^2,\ j-x^2k\bigr),\qquad x=x(q).$$
--   The shift fixes $p$ and $x$, replaces $u$ by $u-p^2w$, satisfies $\sigma_0=\mathrm{id}$ and $\sigma_z\circ\sigma_w=\sigma_{w+z}$ (so it is an action of the additive group of $R$, and $\sigma_{-w}$ inverts $\sigma_w$), and changes the equation by
--   $$E(\sigma_wq)=E(q)+p^3w .$$
--
--   4. **Frames and frame lines.** A frame is a quadruple $\tau=(p,s,u,m)\in R^4$. Put $x_0=s^2+u^3$, $f_1=4s^2$, $f_0=(1+2sx_0)m$, $j_1=2sx_0-1$, $j_0=x_0^2m$, and for $l\in R$
--   $$f_\tau(l)=f_1l+f_0,\qquad j_\tau(l)=j_1l+j_0,\qquad \tau(l)=\bigl(p,s,u,f_\tau(l),j_\tau(l)\bigr).$$
--   Conversely, a point $q=(p,s,u,f,j)$ has the frame $\varphi(q)=\bigl(p,s,u,(1-2sx_0)f+4s^2j\bigr)$ and the linear coordinate $\lambda(q)=x_0^2f-(1+2sx_0)j$, again with $x_0=s^2+u^3$. These constructions are mutually inverse: $\varphi(q)\bigl(\lambda(q)\bigr)=q$, $\varphi(\tau(l))=\tau$ and $\lambda(\tau(l))=l$. Thus $(f,j)\mapsto(m,l)$ is an invertible linear change of the last two coordinates, of determinant $-1$.
--
--   5. **The quadratic part.** Let $Q_\tau(l)=2x_0f_\tau(l)^2-2sf_\tau(l)j_\tau(l)-j_\tau(l)^2$ and $c_\tau=Q_\tau(0)$, and let $M_\tau(l)=q_1+q_2l$ with $q_1=4x_0f_1f_0-2s(f_1j_0+f_0j_1)-2j_1j_0$ and $q_2=2x_0f_1^2-2sf_1j_1-j_1^2$. Then $Q_\tau(l)=c_\tau+l\,M_\tau(l)$, and along the frame line
--   $$E\bigl(\tau(l)\bigr)=l-pu+p^2Q_\tau(l)+p^4f_\tau(l)^3 .$$
--
--   6. **Coordinate polynomials.** Define $\rho_\tau=pu-p^2c_\tau$ and
--   $$h_\tau(l,w)=u-pQ_\tau(l)-p^3f_\tau(l)^3-p^2w,\qquad e_\tau(l,w)=-w-pf_\tau(l)^3-M_\tau(l)\,h_\tau(l,w),$$
--   $$L_\tau(z)=\rho_\tau+p^3z,\qquad W_\tau(z)=-z-\bigl(u-pc_\tau+p^2z\bigr)M_\tau\bigl(L_\tau(z)\bigr)-p\,f_\tau\bigl(L_\tau(z)\bigr)^3 .$$
--   For all $l,w,z\in R$ they satisfy
--   $$p^3e_\tau(l,w)-(l-\rho_\tau)=\bigl(p^2M_\tau(l)-1\bigr)\bigl(E(\tau(l))+p^3w\bigr),\qquad E\bigl(\tau(L_\tau(z))\bigr)+p^3W_\tau(z)=0,$$
--   together with $h_\tau\bigl(L_\tau(z),W_\tau(z)\bigr)=u-pc_\tau+p^2z$ and $e_\tau\bigl(L_\tau(z),W_\tau(z)\bigr)=z$.
--
--   These maps are the building blocks of an explicit isomorphism between the cylinder over $E=0$ and affine space. A pair $(q,w)$ with $E(q)=0$ goes to the frame of $\sigma_{-w}(q)$ together with the coordinate $e_\tau$, and a pair $(\tau,z)$ goes back to $\bigl(\sigma_{W_\tau(z)}(\tau(L_\tau(z))),\,W_\tau(z)\bigr)$. All formulas are polynomials with integer coefficients and none divides by $p$, so the construction applies over every commutative ring. In particular it applies over $A[t]$ and over $\mathbb{C}[p,s,u,F,J]$, where $A=\mathbb{C}[p,s,u,F,J]/(H)$.
--
--   **Formalization Note** Points and frames are the structures `Point R` (fields `p s u f j`) and `Frame R` (fields `p s u m`). In Lean $\delta$ is `cubicDiff`, $\sigma_w q$ is `q.shift w`, $\varphi$ and $\lambda$ are `Point.frame` and `Point.linear`, $\tau(l)$ is `Frame.point`, $M_\tau$ is `Q₁` and $\rho_\tau$ is `root`. The displayed identities are `shift_equation`, `shift_add`, `point_frame`, `frame_point`, `linear_point`, `Q_expand`, `equation_point`, `e_certificate`, `coordinate_equation`, `h_coordinates` and `e_coordinates`; `shift_p`, `shift_u`, `shift_x`, `shift_zero` and `shift_neg_shift` are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/CylinderShift.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/CylinderShift.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation

namespace OAI

noncomputable section

/-! Polynomial stabilization without division by the distinguished coordinate. -/
namespace ComplexCancellation.Cylinder

variable {R : Type*} [CommRing R]

@[ext] structure Point (R : Type*) where
  p : R
  s : R
  u : R
  f : R
  j : R

namespace Point

def x (q : Point R) : R := q.s ^ 2 + q.u ^ 3 + q.p ^ 2 * q.f
def equation (q : Point R) : R :=
  q.x ^ 2 * q.f - (1 + 2 * q.s * q.x) * q.j - q.p ^ 2 * q.j ^ 2 - q.p * q.u

def cubicDiff (p u w : R) : R := -3 * u ^ 2 * w + 3 * u * p ^ 2 * w ^ 2 - p ^ 4 * w ^ 3

lemma cubicDiff_spec (p u w : R) :
    (u - p ^ 2 * w) ^ 3 = u ^ 3 + p ^ 2 * cubicDiff p u w := by
  unfold cubicDiff
  ring

lemma cubicDiff_add (p u w z : R) :
    cubicDiff p u w + cubicDiff p (u - p ^ 2 * w) z = cubicDiff p u (w + z) := by
  unfold cubicDiff
  ring

/-- A finite exponential shift fixing `p`, `x`, `y`, `z` and translating `u` by `-p²w`. -/
def shift (q : Point R) (w : R) : Point R :=
  let k := cubicDiff q.p q.u w
  ⟨q.p, q.s + q.p ^ 2 * q.x * k, q.u - q.p ^ 2 * w,
    q.f - (2 * q.s * q.x + 1) * k - q.p ^ 2 * q.x ^ 2 * k ^ 2,
    q.j - q.x ^ 2 * k⟩

@[simp] lemma shift_p (q : Point R) (w : R) : (q.shift w).p = q.p := rfl
@[simp] lemma shift_u (q : Point R) (w : R) : (q.shift w).u = q.u - q.p ^ 2 * w := rfl

@[simp] lemma shift_x (q : Point R) (w : R) : (q.shift w).x = q.x := by
  change (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) ^ 2 +
    (q.u - q.p ^ 2 * w) ^ 3 + q.p ^ 2 *
    (q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2) = q.x
  rw [cubicDiff_spec]
  calc
    _ = q.s ^ 2 + q.u ^ 3 + q.p ^ 2 * q.f := by ring
    _ = q.x := rfl

@[simp] lemma shift_zero (q : Point R) : q.shift 0 = q := by
  cases q
  simp [shift, cubicDiff]

lemma shift_add (q : Point R) (w z : R) : (q.shift w).shift z = q.shift (w + z) := by
  have hk := cubicDiff_add q.p q.u w z
  have hx := shift_x q w
  apply Point.ext
  · rfl
  · change (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) +
      q.p ^ 2 * (q.shift w).x * cubicDiff q.p (q.u - q.p ^ 2 * w) z = _
    rw [hx]
    change _ = q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u (w + z)
    rw [← hk]
    ring
  · change q.u - q.p ^ 2 * w - q.p ^ 2 * z = q.u - q.p ^ 2 * (w + z)
    ring
  · change q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2 -
      (2 * (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) * (q.shift w).x + 1) *
        cubicDiff q.p (q.u - q.p ^ 2 * w) z -
      q.p ^ 2 * (q.shift w).x ^ 2 * cubicDiff q.p (q.u - q.p ^ 2 * w) z ^ 2 = _
    rw [hx]
    change _ = q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u (w + z) -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u (w + z) ^ 2
    rw [← hk]
    ring
  · change q.j - q.x ^ 2 * cubicDiff q.p q.u w -
      (q.shift w).x ^ 2 * cubicDiff q.p (q.u - q.p ^ 2 * w) z = _
    rw [hx]
    change _ = q.j - q.x ^ 2 * cubicDiff q.p q.u (w + z)
    rw [← hk]
    ring

lemma shift_equation (q : Point R) (w : R) :
    (q.shift w).equation = q.equation + q.p ^ 3 * w := by
  unfold equation
  rw [shift_x]
  change q.x ^ 2 * (q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2) -
    (1 + 2 * (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) * q.x) *
      (q.j - q.x ^ 2 * cubicDiff q.p q.u w) -
    q.p ^ 2 * (q.j - q.x ^ 2 * cubicDiff q.p q.u w) ^ 2 -
    q.p * (q.u - q.p ^ 2 * w) = _
  ring

@[simp] lemma shift_neg_shift (q : Point R) (w : R) : (q.shift w).shift (-w) = q := by
  rw [shift_add, add_neg_cancel, shift_zero]

end Point
end ComplexCancellation.Cylinder

namespace ComplexCancellation.Cylinder
variable {R : Type*} [CommRing R]

@[ext] structure Frame (R : Type*) where
  p : R
  s : R
  u : R
  m : R

namespace Frame

def x₀ (t : Frame R) : R := t.s ^ 2 + t.u ^ 3
def f₁ (t : Frame R) : R := 4 * t.s ^ 2
def f₀ (t : Frame R) : R := (1 + 2 * t.s * t.x₀) * t.m
def j₁ (t : Frame R) : R := 2 * t.s * t.x₀ - 1
def j₀ (t : Frame R) : R := t.x₀ ^ 2 * t.m
def f (t : Frame R) (l : R) : R := t.f₁ * l + t.f₀
def j (t : Frame R) (l : R) : R := t.j₁ * l + t.j₀
def point (t : Frame R) (l : R) : Point R := ⟨t.p, t.s, t.u, t.f l, t.j l⟩
def Q (t : Frame R) (l : R) : R :=
  2 * t.x₀ * t.f l ^ 2 - 2 * t.s * t.f l * t.j l - t.j l ^ 2
def c (t : Frame R) : R := t.Q 0
def q₁ (t : Frame R) : R :=
  4 * t.x₀ * t.f₁ * t.f₀ - 2 * t.s * (t.f₁ * t.j₀ + t.f₀ * t.j₁) - 2 * t.j₁ * t.j₀
def q₂ (t : Frame R) : R :=
  2 * t.x₀ * t.f₁ ^ 2 - 2 * t.s * t.f₁ * t.j₁ - t.j₁ ^ 2
def Q₁ (t : Frame R) (l : R) : R := t.q₁ + t.q₂ * l

lemma Q_expand (t : Frame R) (l : R) : t.Q l = t.c + l * t.Q₁ l := by
  simp only [Q, c, Q₁, q₁, q₂, f, j]
  ring

lemma equation_point (t : Frame R) (l : R) :
    (t.point l).equation = l - t.p * t.u + t.p ^ 2 * t.Q l + t.p ^ 4 * t.f l ^ 3 := by
  have hl : t.x₀ ^ 2 * t.f l - (1 + 2 * t.s * t.x₀) * t.j l = l := by
    unfold f j f₁ f₀ j₁ j₀
    ring
  change (t.s ^ 2 + t.u ^ 3 + t.p ^ 2 * t.f l) ^ 2 * t.f l -
    (1 + 2 * t.s * (t.s ^ 2 + t.u ^ 3 + t.p ^ 2 * t.f l)) * t.j l -
    t.p ^ 2 * t.j l ^ 2 - t.p * t.u = _
  change (t.x₀ + t.p ^ 2 * t.f l) ^ 2 * t.f l -
    (1 + 2 * t.s * (t.x₀ + t.p ^ 2 * t.f l)) * t.j l -
    t.p ^ 2 * t.j l ^ 2 - t.p * t.u = _
  unfold Q
  linear_combination hl

def root (t : Frame R) : R := t.p * t.u - t.p ^ 2 * t.c
def h (t : Frame R) (l w : R) : R :=
  t.u - t.p * t.Q l - t.p ^ 3 * t.f l ^ 3 - t.p ^ 2 * w
def e (t : Frame R) (l w : R) : R := -w - t.p * t.f l ^ 3 - t.Q₁ l * t.h l w

def L (t : Frame R) (z : R) : R := t.root + t.p ^ 3 * z
def W (t : Frame R) (z : R) : R :=
  -z - (t.u - t.p * t.c + t.p ^ 2 * z) * t.Q₁ (t.L z) - t.p * t.f (t.L z) ^ 3

lemma e_certificate (t : Frame R) (l w : R) :
    t.p ^ 3 * t.e l w - (l - t.root) =
    (t.p ^ 2 * t.Q₁ l - 1) * ((t.point l).equation + t.p ^ 3 * w) := by
  rw [equation_point]
  unfold e h root
  rw [Q_expand]
  ring

lemma coordinate_equation (t : Frame R) (z : R) :
    (t.point (t.L z)).equation + t.p ^ 3 * t.W z = 0 := by
  rw [equation_point, Q_expand]
  unfold W L root
  ring

lemma h_coordinates (t : Frame R) (z : R) :
    t.h (t.L z) (t.W z) = t.u - t.p * t.c + t.p ^ 2 * z := by
  unfold h W
  rw [Q_expand]
  unfold L root
  ring

lemma e_coordinates (t : Frame R) (z : R) : t.e (t.L z) (t.W z) = z := by
  unfold e
  rw [h_coordinates]
  unfold W
  ring

end Frame

namespace Point

def frame (q : Point R) : Frame R :=
  ⟨q.p, q.s, q.u, (1 - 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.f + 4 * q.s ^ 2 * q.j⟩
def linear (q : Point R) : R :=
  (q.s ^ 2 + q.u ^ 3) ^ 2 * q.f - (1 + 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.j

lemma point_frame (q : Point R) : q.frame.point q.linear = q := by
  apply Point.ext
  · rfl
  · rfl
  · rfl
  · change 4 * q.s ^ 2 * q.linear +
      (1 + 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.frame.m = q.f
    unfold linear frame
    ring
  · change (2 * q.s * (q.s ^ 2 + q.u ^ 3) - 1) * q.linear +
      (q.s ^ 2 + q.u ^ 3) ^ 2 * q.frame.m = q.j
    unfold linear frame
    ring

end Point
namespace Frame

@[simp] lemma frame_point (t : Frame R) (l : R) : (t.point l).frame = t := by
  apply Frame.ext
  · rfl
  · rfl
  · rfl
  · change (1 - 2 * t.s * t.x₀) * t.f l + 4 * t.s ^ 2 * t.j l = t.m
    unfold f j f₁ f₀ j₁ j₀
    ring

@[simp] lemma linear_point (t : Frame R) (l : R) : (t.point l).linear = l := by
  change t.x₀ ^ 2 * t.f l - (1 + 2 * t.s * t.x₀) * t.j l = l
  unfold f j f₁ f₀ j₁ j₀
  ring

end Frame
end ComplexCancellation.Cylinder

end

end OAI


