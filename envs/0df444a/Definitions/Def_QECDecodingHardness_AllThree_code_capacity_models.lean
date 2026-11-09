-- Prove2me | Definitions.Def_QECDecodingHardness_AllThree_code_capacity_models
-- name    : QECDecodingHardness_AllThree_code_capacity_models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:45.827196+00:00
-- url     : https://prove2.me/theorems/557f45ae-3501-46a4-9b46-af1ec2ba3ed5
-- title:
--   ColorCodeZ and SurfaceCodeXYZ from lattice incidence
-- statement:
--   ColorCodeZ uses the triangular patch of order k, with one Z-error bit per qubit triangle and an X check at each stabilizer vertex. SurfaceCodeXYZ uses the square patch of size L, with two Pauli bits per qubit edge. Their syndrome rules are
--
--   $$\sigma_{\mathrm{col}}(v)=\sum_{t\ni v}z_t,\qquad \sigma_X(v)=\sum_{e\ni v}z_e,\qquad \sigma_Z(f)=\sum_{e\subset\partial f}x_e.$$
--
--   All sums are binary. The surface syndrome is ordered by vertex checks followed by face checks. The surface objective counts the union of the X and Z supports, so a Y error is one qubit fault. The color objective is the number of nonzero Z bits.
--
--   Both matrices are generated from the coordinate lists and actual incidence. These definitions are the two code-capacity tasks of Theorem 1, with every syndrome and every positive square size allowed; there are no per-location weights or noise probabilities.
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), pp.3–5, Section II.1–2 and Theorem 1(1)–(2)

import Definitions.Def_QECDecodingHardness_AllThree_lattice_coordinates

namespace QECDecodingHardness.AllThree

/-- Section II.1, pp.3–4: Z-only errors on the actual triangular color code.
A column is a triangle and a row is an incident vertex carrying an X check. -/
def colorCodeZ (k : ℕ) : CheckSystem :=
  systemOfLists (colorQubits k) (colorChecks k) false (fun _ _ => 0)
    (fun v t => if v ∈ triangleVertices t then 1 else 0)

/-- Section II.2, p.4: both Pauli bits act on one qubit location. The check
ordering is vertices/X checks, then faces/Z checks. Z bits trigger vertices,
X bits trigger faces. The objective still counts the union of their supports. -/
def surfaceCodeXYZ (L : ℕ) : CheckSystem :=
  systemOfLists (surfaceQubits L)
    ((surfaceXChecks L).map Sum.inl ++ (surfaceZChecks L).map Sum.inr) true
    (fun c e => match c with
      | .inl _ => 0
      | .inr f => if edgeAtFace f e then 1 else 0)
    (fun c e => match c with
      | .inl v => if edgeAtVertex v e then 1 else 0
      | .inr _ => 0)

end QECDecodingHardness.AllThree


