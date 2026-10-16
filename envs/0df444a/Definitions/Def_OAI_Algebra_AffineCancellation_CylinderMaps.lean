-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
-- name    : OAI_Algebra_AffineCancellation_CylinderMaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:49:16.008121+00:00
-- url     : https://prove2.me/theorems/ec06dcb4-702e-43f5-8067-21e66eeab429
-- title:
--   Mutually inverse encoding and decoding maps between the cylinder over $E=0$ and frame space
-- statement:
--   Let $R$ be a commutative ring. A point is $q=(p,s,u,f,j)\in R^5$ with
--   $$x=s^2+u^3+p^2f,\qquad E(q)=x^2f-(1+2sx)j-p^2j^2-pu,$$
--   and a frame is $\tau=(p,s,u,m)\in R^4$. The following explicit polynomial maps from the cylinder shift construction are used. For $w\in R$ and $k=-3u^2w+3up^2w^2-p^4w^3$, the shift is $\sigma_w(q)=\bigl(p,\,s+p^2xk,\,u-p^2w,\,f-(2sx+1)k-p^2x^2k^2,\,j-x^2k\bigr)$; it satisfies $E(\sigma_wq)=E(q)+p^3w$ and $\sigma_z\circ\sigma_w=\sigma_{w+z}$. With $x_0=s^2+u^3$, a point has the frame $\varphi(q)=\bigl(p,s,u,(1-2sx_0)f+4s^2j\bigr)$ and the linear coordinate $\lambda(q)=x_0^2f-(1+2sx_0)j$. A frame and $l\in R$ give the point $\tau(l)=\bigl(p,s,u,f_\tau(l),j_\tau(l)\bigr)$ with $f_\tau(l)=4s^2l+(1+2sx_0)m$ and $j_\tau(l)=(2sx_0-1)l+x_0^2m$. Finally, with $Q_\tau(l)=2x_0f_\tau(l)^2-2sf_\tau(l)j_\tau(l)-j_\tau(l)^2=c_\tau+l\,M_\tau(l)$ ($c_\tau=Q_\tau(0)$, $M_\tau$ linear in $l$), the coordinate polynomials are
--   $$L_\tau(z)=pu-p^2c_\tau+p^3z,\qquad W_\tau(z)=-z-(u-pc_\tau+p^2z)\,M_\tau(L_\tau(z))-p\,f_\tau(L_\tau(z))^3,$$
--   $$e_\tau(l,w)=-w-pf_\tau(l)^3-M_\tau(l)\bigl(u-pQ_\tau(l)-p^3f_\tau(l)^3-p^2w\bigr).$$
--
--   The file defines and studies the following.
--
--   1. **Encoding.** For a point $q$ and $w\in R$ let $r=\sigma_{-w}(q)$ and
--   $$\mathrm{enc}(q,w)=\Bigl(\varphi(r),\ e_{\varphi(r)}\bigl(\lambda(r),w\bigr)\Bigr)\in R^4\times R .$$
--
--   2. **Decoding.** For a frame $\tau$ and $z\in R$,
--   $$\mathrm{dec}(\tau,z)=\Bigl(\sigma_{W_\tau(z)}\bigl(\tau(L_\tau(z))\bigr),\ W_\tau(z)\Bigr)\in R^5\times R .$$
--
--   3. **Decoding lands on the hypersurface.** For every frame $\tau$ and every $z$, the point component of $\mathrm{dec}(\tau,z)$ satisfies $E=0$.
--
--   4. **Left inverse.** $\mathrm{enc}\bigl(\mathrm{dec}(\tau,z)\bigr)=(\tau,z)$ for all frames $\tau$ and all $z\in R$, with no hypotheses.
--
--   5. **Right inverse on the cylinder.** Let $q$ be a point with $E(q)=0$ whose first coordinate $p$ has a cancellable cube, i.e. $p^3r=0$ implies $r=0$ for every $r\in R$. Then $\mathrm{dec}\bigl(\mathrm{enc}(q,w)\bigr)=(q,w)$ for every $w\in R$.
--
--   6. **Naturality.** For a ring homomorphism $g:R\to S$, apply $g$ coordinatewise to points and frames, written $q^g$ and $\tau^g$. Then $x(q^g)=g(x(q))$, $E(q^g)=g(E(q))$, $\sigma_w(q)^g=\sigma_{g(w)}(q^g)$, $\tau(l)^g=\tau^g(g(l))$, $g(L_\tau(z))=L_{\tau^g}(g(z))$ and $g(W_\tau(z))=W_{\tau^g}(g(z))$, and both $\mathrm{enc}$ and $\mathrm{dec}$ commute with $g$.
--
--   Consequently, if $p^3$ is cancellable for all points under consideration (for instance when $p$ is a non-zero-divisor), then $\mathrm{enc}$ and $\mathrm{dec}$ are inverse bijections between the pairs $(q,w)\in R^5\times R$ with $E(q)=0$ and $R^4\times R$, given by polynomials in both directions. Naturality allows these maps to be applied to universal points, where they become ring homomorphisms. This yields an isomorphism between the polynomial ring in one variable over $\mathbb{C}[p,s,u,F,J]/(H)$, where $H$ is $E$ evaluated at the five variables, and a polynomial ring in five variables.
--
--   **Formalization Note** $\mathrm{enc}$ and $\mathrm{dec}$ are `encode : Point R → R → Frame R × R` and `decode : Frame R → R → Point R × R`. The inverse laws are `encode_decode` and `decode_encode`, the latter with hypotheses `hq : q.equation = 0` and `hp : ∀ r, q.p ^ 3 * r = 0 → r = 0`. Coordinatewise application of $g$ is `Point.map` and `Frame.map`, and the naturality lemmas are `map_x`, `map_equation`, `map_shift`, `map_point`, `map_L`, `map_W`, `decode_map` and `encode_map`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/CylinderMaps.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/CylinderMaps.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift

namespace OAI

noncomputable section

namespace ComplexCancellation.Cylinder
variable {R S : Type*} [CommRing R] [CommRing S]

def encode (q : Point R) (w : R) : Frame R × R :=
  let t := q.shift (-w)
  (t.frame, t.frame.e t.linear w)

def decode (t : Frame R) (z : R) : Point R × R :=
  ((t.point (t.L z)).shift (t.W z), t.W z)

lemma decode_equation (t : Frame R) (z : R) : (decode t z).1.equation = 0 := by
  change ((t.point (t.L z)).shift (t.W z)).equation = 0
  rw [Point.shift_equation]
  exact t.coordinate_equation z

lemma encode_decode (t : Frame R) (z : R) :
    encode (decode t z).1 (decode t z).2 = (t, z) := by
  simp only [decode, encode, Point.shift_neg_shift, Frame.frame_point,
    Frame.linear_point, Frame.e_coordinates]

lemma decode_encode (q : Point R) (w : R) (hq : q.equation = 0)
    (hp : ∀ r : R, q.p ^ 3 * r = 0 → r = 0) :
    decode (encode q w).1 (encode q w).2 = (q, w) := by
  let r := q.shift (-w)
  let t := r.frame
  let l := r.linear
  let z := t.e l w
  have hpt : t.p = q.p := rfl
  have htl : t.point l = r := r.point_frame
  have heq : (t.point l).equation + t.p ^ 3 * w = 0 := by
    rw [htl]
    change (q.shift (-w)).equation + q.p ^ 3 * w = 0
    rw [Point.shift_equation, hq]
    ring
  have hL : t.L z = l := by
    have hc := t.e_certificate l w
    rw [heq, mul_zero] at hc
    change t.root + t.p ^ 3 * t.e l w = l
    linear_combination hc
  have hW : t.W z = w := by
    have h := t.coordinate_equation z
    rw [hL] at h
    apply sub_eq_zero.mp
    apply hp
    rw [← hpt, mul_sub]
    linear_combination h - heq
  change (((t.point (t.L z)).shift (t.W z)), t.W z) = (q, w)
  rw [hL, hW, htl]
  congr 1
  change (q.shift (-w)).shift w = q
  rw [Point.shift_add, neg_add_cancel, Point.shift_zero]

namespace Point

def map (q : Point R) (g : R →+* S) : Point S :=
  ⟨g q.p, g q.s, g q.u, g q.f, g q.j⟩

@[simp] lemma map_x (q : Point R) (g : R →+* S) : (q.map g).x = g q.x := by
  simp [map, x]

@[simp] lemma map_equation (q : Point R) (g : R →+* S) :
    (q.map g).equation = g q.equation := by
  simp [equation, map, x, map_ofNat]

@[simp] lemma map_shift (q : Point R) (w : R) (g : R →+* S) :
    (q.shift w).map g = (q.map g).shift (g w) := by
  ext <;> simp [map, shift, cubicDiff, x, map_ofNat]

end Point
namespace Frame

def map (t : Frame R) (g : R →+* S) : Frame S := ⟨g t.p, g t.s, g t.u, g t.m⟩

@[simp] lemma map_point (t : Frame R) (l : R) (g : R →+* S) :
    (t.point l).map g = (t.map g).point (g l) := by
  ext <;> simp [Point.map, map, point, f, j, f₁, f₀, j₁, j₀, x₀, map_ofNat]

@[simp] lemma map_L (t : Frame R) (z : R) (g : R →+* S) :
    g (t.L z) = (t.map g).L (g z) := by
  simp [map, L, root, c, Q, f, j, f₁, f₀, j₁, j₀, x₀, map_ofNat]

@[simp] lemma map_W (t : Frame R) (z : R) (g : R →+* S) :
    g (t.W z) = (t.map g).W (g z) := by
  simp [W, map_L, map, c, Q, Q₁, q₁, q₂, f, j, f₁, f₀, j₁, j₀, x₀, map_ofNat]

end Frame

lemma decode_map (t : Frame R) (z : R) (g : R →+* S) :
    ((decode t z).1.map g, g (decode t z).2) = decode (t.map g) (g z) := by
  simp [decode]

lemma encode_map (q : Point R) (w : R) (g : R →+* S) :
    ((encode q w).1.map g, g (encode q w).2) = encode (q.map g) (g w) := by
  simp only [encode, ← Point.map_shift, ← map_neg]
  apply Prod.ext
  · ext <;> simp [Point.frame, Frame.map, Point.map, map_ofNat]
  · simp [Frame.e, Frame.h, Frame.Q₁, Frame.q₁, Frame.q₂, Frame.Q, Frame.f, Frame.j,
      Frame.f₀, Frame.f₁, Frame.j₀, Frame.j₁, Frame.x₀, Point.linear, Point.frame, Point.map, map_ofNat]

end ComplexCancellation.Cylinder

end

end OAI


