-- Prove2me | Definitions.Def_GirvingAKS_MGG_Defs
-- name    : GirvingAKS_MGG_Defs
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:42.495449+00:00
-- url     : https://prove2.me/theorems/6f2478aa-7f9f-4f6b-8f68-d5b2601f67a0
-- title:
--   AKS sorting networks (Seiferas port) — Margulis-Gabber-Galil Expander HalfEdgeGraph
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/MGG/Defs.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** The Gabber & Galil (1981) construction, as analyzed by Jimbo & Maruoka (1987): an 8-regular graph on `(Z/nZ)²` using factor-2 shear maps `T₁(x,y) = (x+2y, y)`, `T₂(x,y) = (x, 2x+y)` and their +1 shifts `T₃(x,y) = (x+2y+1, y)`, `T₄(x,y) = (x, 2x+y+1)`.
--
--   The factor of 2 in the shear maps is essential for achieving a constant spectral gap. Simple shears `(x+y, y)` give gap → 0 as n → ∞.
--
--   Vertices are `Fin (n * n)`, encoding `(x, y)` as `x * n + y`. The 8 ports correspond to `T₁, T₁⁻¹, T₂, T₂⁻¹, T₃, T₃⁻¹, T₄, T₄⁻¹` with port pairing `2k ↔ 2k+1` so that each map is paired with its inverse.
--
--   - Gabber & Galil (1981), "Explicit constructions of linear-sized superconcentrators,"
--
--   *J. Comput. System Sci.* 22(3), 407–420.
--
--   - Jimbo & Maruoka (1987), "Expanders obtained from affine transformations,"
--
--   *Combinatorica* 7, 343–355.
--
--   See `docs/mgg.md` for the full proof plan and additional references.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Defs.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Graph_Regular

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/MGG/Defs.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Margulis-Gabber-Galil Expander HalfEdgeGraph

  The Gabber & Galil (1981) construction, as analyzed by Jimbo & Maruoka (1987):
  an 8-regular graph on `(Z/nZ)²` using factor-2 shear maps
  `T₁(x,y) = (x+2y, y)`, `T₂(x,y) = (x, 2x+y)` and their +1 shifts
  `T₃(x,y) = (x+2y+1, y)`, `T₄(x,y) = (x, 2x+y+1)`.

  The factor of 2 in the shear maps is essential for achieving a constant
  spectral gap. Simple shears `(x+y, y)` give gap → 0 as n → ∞.

  Vertices are `Fin (n * n)`, encoding `(x, y)` as `x * n + y`.
  The 8 ports correspond to `T₁, T₁⁻¹, T₂, T₂⁻¹, T₃, T₃⁻¹, T₄, T₄⁻¹`
  with port pairing `2k ↔ 2k+1` so that each map is paired with its inverse.

  ## References

  - Gabber & Galil (1981), "Explicit constructions of linear-sized superconcentrators,"
    *J. Comput. System Sci.* 22(3), 407–420.
  - Jimbo & Maruoka (1987), "Expanders obtained from affine transformations,"
    *Combinatorica* 7, 343–355.

  See `docs/mgg.md` for the full proof plan and additional references.
-/


section


open Matrix BigOperators Finset


/-! **MGG Neighbor Computation** -/

/-- Neighbor computation for the Gabber-Galil graph on (Z/nZ)².
    Given `n`, coordinates `(x, y)` with `x, y < n`, and a port number `< 8`,
    returns `(x', y', reverse_port)` where `(x', y')` is the neighbor and
    `reverse_port` is the port index at the far end. All arithmetic mod `n`.
    Uses factor-2 shear maps: T₁(x,y) = (x+2y, y), T₂(x,y) = (x, 2x+y). -/
def mggNbr (n x y port : ℕ) : ℕ × ℕ × ℕ :=
  match port with
  | 0 => ((x + 2 * y) % n, y, 1)             -- T₁
  | 1 => ((x + 2 * n - 2 * y) % n, y, 0)     -- T₁⁻¹
  | 2 => (x, (2 * x + y) % n, 3)             -- T₂
  | 3 => (x, (y + 2 * n - 2 * x) % n, 2)     -- T₂⁻¹
  | 4 => ((x + 2 * y + 1) % n, y, 5)         -- T₃
  | 5 => ((x + 2 * n - 2 * y - 1) % n, y, 4) -- T₃⁻¹
  | 6 => (x, (2 * x + y + 1) % n, 7)         -- T₄
  | 7 => (x, (y + 2 * n - 2 * x - 1) % n, 6) -- T₄⁻¹
  | _ + 8 => (x, y, 0)


/-! **Bound Lemmas** -/

theorem mggNbr_fst_lt (n x y port : ℕ) (hn : 0 < n) (hx : x < n) (hp : port < 8) :
    (mggNbr n x y port).1 < n := by
  interval_cases port <;> simp only [mggNbr] <;>
    first | exact Nat.mod_lt _ hn | exact hx

theorem mggNbr_snd_fst_lt (n x y port : ℕ) (hn : 0 < n) (hy : y < n) (hp : port < 8) :
    (mggNbr n x y port).2.1 < n := by
  interval_cases port <;> simp only [mggNbr] <;>
    first | exact Nat.mod_lt _ hn | exact hy

theorem mggNbr_snd_snd_lt (n x y port : ℕ) (hp : port < 8) :
    (mggNbr n x y port).2.2 < 8 := by
  interval_cases port <;> simp only [mggNbr] <;> omega


/-! **Modular Arithmetic Helpers** -/

/-- `((a + c) % n + 2 * n - c) % n = a` when `a < n` and `c ≤ 2 * n`. -/
theorem mod_add_sub_cancel (a c n : ℕ) (ha : a < n) (hc : c ≤ 2 * n) :
    ((a + c) % n + 2 * n - c) % n = a := by
  -- Three cases based on the value of a + c relative to n and 2n
  by_cases h1 : a + c < n
  · -- (a + c) % n = a + c, result = a + c + 2n - c = a + 2n
    rw [Nat.mod_eq_of_lt h1,
        show a + c + 2 * n - c = a + n + n from by omega,
        Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · push_neg at h1
    by_cases h2 : a + c < 2 * n
    · -- (a + c) % n = a + c - n, result = a + c - n + 2n - c = a + n
      have hmod : (a + c) % n = a + c - n := by
        conv_lhs => rw [show a + c = a + c - n + n from by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, show a + c - n + 2 * n - c = a + n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt ha]
    · -- (a + c) % n = a + c - 2n, result = a + c - 2n + 2n - c = a
      push_neg at h2
      have hmod : (a + c) % n = a + c - 2 * n := by
        conv_lhs => rw [show a + c = a + c - 2 * n + n + n from by omega]
        rw [Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, show a + c - 2 * n + 2 * n - c = a from by omega,
          Nat.mod_eq_of_lt ha]

/-- `((a + 2 * n - c) % n + c) % n = a` when `a < n` and `c ≤ 2 * n`. -/
theorem mod_sub_add_cancel (a c n : ℕ) (ha : a < n) (hc : c ≤ 2 * n) :
    ((a + 2 * n - c) % n + c) % n = a := by
  -- Three cases based on the value of a + 2n - c relative to n and 2n
  by_cases h1 : a + 2 * n - c < n
  · -- a + 2n - c < n, so (a + 2n - c) % n = a + 2n - c
    rw [Nat.mod_eq_of_lt h1,
        show a + 2 * n - c + c = a + 2 * n from by omega,
        show a + 2 * n = a + n + n from by omega,
        Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · push_neg at h1
    by_cases h2 : a + 2 * n - c < 2 * n
    · -- n ≤ a + 2n - c < 2n
      have hmod : (a + 2 * n - c) % n = a + 2 * n - c - n := by
        conv_lhs => rw [show a + 2 * n - c = a + 2 * n - c - n + n from by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, show a + 2 * n - c - n + c = a + n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt ha]
    · -- a + 2n - c ≥ 2n, so c ≤ a
      push_neg at h2
      have hmod : (a + 2 * n - c) % n = a + 2 * n - c - 2 * n := by
        conv_lhs => rw [show a + 2 * n - c = a + 2 * n - c - 2 * n + n + n from by omega]
        rw [Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, show a + 2 * n - c - 2 * n + c = a from by omega,
          Nat.mod_eq_of_lt ha]


/-! **Involution at ℕ Level** -/

/-- The double application of `mggNbr` returns to the original coordinates and port. -/
theorem mggNbr_invol (n x y port : ℕ) (hx : x < n) (hy : y < n) (hp : port < 8) :
    let r := mggNbr n x y port
    mggNbr n r.1 r.2.1 r.2.2 = (x, y, port) := by
  interval_cases port <;> simp only [mggNbr]
  -- Port 0→1: T₁ then T₁⁻¹
  · exact Prod.ext (mod_add_sub_cancel x (2 * y) n hx (by omega)) rfl
  -- Port 1→0: T₁⁻¹ then T₁
  · exact Prod.ext (mod_sub_add_cancel x (2 * y) n hx (by omega)) rfl
  -- Port 2→3: T₂ then T₂⁻¹
  · refine Prod.ext rfl (Prod.ext ?_ rfl)
    rw [show 2 * x + y = y + 2 * x from by omega]
    exact mod_add_sub_cancel y (2 * x) n hy (by omega)
  -- Port 3→2: T₂⁻¹ then T₂
  · refine Prod.ext rfl (Prod.ext ?_ rfl)
    rw [show 2 * x + (y + 2 * n - 2 * x) % n = (y + 2 * n - 2 * x) % n + 2 * x from by omega]
    exact mod_sub_add_cancel y (2 * x) n hy (by omega)
  -- Port 4→5: T₃ then T₃⁻¹
  · refine Prod.ext ?_ rfl
    rw [show x + 2 * y + 1 = x + (2 * y + 1) from by omega, Nat.sub_sub]
    exact mod_add_sub_cancel x (2 * y + 1) n hx (by omega)
  -- Port 5→4: T₃⁻¹ then T₃
  · refine Prod.ext ?_ rfl
    rw [show x + 2 * n - 2 * y - 1 = x + 2 * n - (2 * y + 1) from by omega,
        show (x + 2 * n - (2 * y + 1)) % n + 2 * y + 1 =
            (x + 2 * n - (2 * y + 1)) % n + (2 * y + 1) from by omega]
    exact mod_sub_add_cancel x (2 * y + 1) n hx (by omega)
  -- Port 6→7: T₄ then T₄⁻¹
  · refine Prod.ext rfl (Prod.ext ?_ rfl)
    rw [show 2 * x + y + 1 = y + (2 * x + 1) from by omega, Nat.sub_sub]
    exact mod_add_sub_cancel y (2 * x + 1) n hy (by omega)
  -- Port 7→6: T₄⁻¹ then T₄
  · refine Prod.ext rfl (Prod.ext ?_ rfl)
    rw [show y + 2 * n - 2 * x - 1 = y + 2 * n - (2 * x + 1) from by omega,
        show 2 * x + (y + 2 * n - (2 * x + 1)) % n + 1 =
            (y + 2 * n - (2 * x + 1)) % n + (2 * x + 1) from by omega]
    exact mod_sub_add_cancel y (2 * x + 1) n hy (by omega)


/-! **Encode/Decode Helpers** -/

theorem encode_div (a b n : ℕ) (hb : b < n) : (a * n + b) / n = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt hb]
  omega

theorem encode_mod (a b n : ℕ) (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]


/-! **Rotation Map** -/

/-- The rotation map for the MGG graph: decode vertex as (x, y) in (Z/nZ)²,
    apply the port-dependent shear map, re-encode. -/
def mgg_rot (n : ℕ) (p : Fin (n * n) × Fin 8) : Fin (n * n) × Fin 8 :=
  have hn : 0 < n :=
    Nat.pos_of_ne_zero (by rintro rfl; exact absurd p.1.isLt (by simp))
  let x := p.1.val / n
  let y := p.1.val % n
  let r := mggNbr n x y p.2.val
  have hx : x < n := (Nat.div_lt_iff_lt_mul hn).mpr p.1.isLt
  have hy : y < n := Nat.mod_lt _ hn
  have hx' := mggNbr_fst_lt n x y p.2.val hn hx p.2.isLt
  have hy' := mggNbr_snd_fst_lt n x y p.2.val hn hy p.2.isLt
  let x' : Fin n := ⟨r.1, hx'⟩
  let y' : Fin n := ⟨r.2.1, hy'⟩
  (⟨x'.val * n + y'.val, Fin.pair_lt x' y'⟩,
   ⟨r.2.2, mggNbr_snd_snd_lt n x y p.2.val p.2.isLt⟩)

/-- The MGG rotation is an involution. -/
theorem mgg_rot_involution (n : ℕ) (p : Fin (n * n) × Fin 8) :
    mgg_rot n (mgg_rot n p) = p := by
  obtain ⟨v, port⟩ := p
  have hn : 0 < n :=
    Nat.pos_of_ne_zero (by rintro rfl; exact absurd v.isLt (by simp))
  have hx : v.val / n < n := (Nat.div_lt_iff_lt_mul hn).mpr v.isLt
  have hy : v.val % n < n := Nat.mod_lt _ hn
  have hy' := mggNbr_snd_fst_lt n (v.val / n) (v.val % n) port.val hn hy port.isLt
  -- Encode-decode: the intermediate result decodes correctly
  have hdec_x := encode_div (mggNbr n (v.val / n) (v.val % n) port.val).1
    (mggNbr n (v.val / n) (v.val % n) port.val).2.1 n hy'
  have hdec_y := encode_mod (mggNbr n (v.val / n) (v.val % n) port.val).1
    (mggNbr n (v.val / n) (v.val % n) port.val).2.1 n hy'
  -- Double application of mggNbr returns to original
  have hinvol := mggNbr_invol n (v.val / n) (v.val % n) port.val hx hy port.isLt
  -- Original vertex reconstruction
  have henc : (v.val / n) * n + v.val % n = v.val := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod v.val n
  -- Prove component-wise via Fin.ext
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · -- Vertex value
    show (mgg_rot n (mgg_rot n (v, port))).1.val = v.val
    simp only [mgg_rot, hdec_x, hdec_y, hinvol]
    exact henc
  · -- Port value
    show (mgg_rot n (mgg_rot n (v, port))).2.val = port.val
    simp only [mgg_rot, hdec_x, hdec_y, hinvol]


/-! **MGG Regular HalfEdgeGraph** -/

/-- The Gabber-Galil 8-regular graph on `n²` vertices.
    Vertices are elements of `(Z/nZ)²`, encoded as `Fin (n * n)`.
    The 8 neighbors of `(x, y)` are given by the factor-2 shear maps
    `T₁(x,y) = (x+2y, y)`, `T₂(x,y) = (x, 2x+y)` and their +1 shifts,
    together with their inverses. -/
def mgg (n : ℕ) : RegularGraph (n * n) 8 where
  rot := mgg_rot n
  rot_involution := mgg_rot_involution n

end


