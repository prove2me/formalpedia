-- Prove2me | Definitions.Def_OAIQ078B000
-- name    : OAIQ078B000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:18:50.866662+00:00
-- url     : https://prove2.me/theorems/c546ab7b-a445-4cd4-8e30-170821a2b6e8
-- title:
--   Definitions bundle OAIQ078B000 of the split of OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 770 declarations of OpenAI's Lean: 555 definitions, 18 inductive types or structures, 12 instances and 185 theorems. The definitions and types are `OAI.ActionOrbitTransport.PairOrbit`, `OAI.ActionOrbitTransport.pairOrbit`, `OAI.ActionOrbitTransport.stabilizerOrbit`, `OAI.ActionOrbitTransport.suborbitCard`, `OAI.CriticalPercolation.AlgebraicDescent`, `OAI.CriticalPercolation.BernoulliProduct.DecisionCode`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.codeOf`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.failure`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.partition`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.partitionWithBlock`, `OAI.CriticalPercolation.BernoulliProduct.DecisionRule.state`, `OAI.CriticalPercolation.BernoulliProduct.HasFiniteOpenWitness`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition.decide`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition.enlarge`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition.historySigma`, `OAI.CriticalPercolation.BernoulliProduct.RevealPartition.probability`, `OAI.CriticalPercolation.BernoulliProduct.allOpen`, `OAI.CriticalPercolation.BernoulliProduct.atParameter`, `OAI.CriticalPercolation.BernoulliProduct.atParameters`, `OAI.CriticalPercolation.BernoulliProduct.bitMeasure`, `OAI.CriticalPercolation.BernoulliProduct.bitWeight`, `OAI.CriticalPercolation.BernoulliProduct.blockProbability`, `OAI.CriticalPercolation.BernoulliProduct.blockSigma`, `OAI.CriticalPercolation.BernoulliProduct.blueProjection`, `OAI.CriticalPercolation.BernoulliProduct.closedBlock`, `OAI.CriticalPercolation.BernoulliProduct.coordinateSigma`, `OAI.CriticalPercolation.BernoulliProduct.erasedWhiteParameters`, `OAI.CriticalPercolation.BernoulliProduct.finiteBadUnion`, `OAI.CriticalPercolation.BernoulliProduct.finiteCoordinateEvents`, `OAI.CriticalPercolation.BernoulliProduct.forceOn`, `OAI.CriticalPercolation.BernoulliProduct.law`, `OAI.CriticalPercolation.BernoulliProduct.markLaw`, `OAI.CriticalPercolation.BernoulliProduct.pairedParameters`, `OAI.CriticalPercolation.BernoulliProduct.pairedUnion`, `OAI.CriticalPercolation.BernoulliProduct.pinnedParameters`, `OAI.CriticalPercolation.BernoulliProduct.predictionFailure`, `OAI.CriticalPercolation.BernoulliProduct.reindexMarks`, `OAI.CriticalPercolation.BernoulliProduct.selectedEvent` and 533 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `BenjaminiSchramm_AvoidanceProduct`, `BenjaminiSchramm_CeilingBandTransport`, `BenjaminiSchramm_ConsistentLayers`, `BenjaminiSchramm_CriticalHeightHit`, `BenjaminiSchramm_ExteriorEscape`, `BenjaminiSchramm_FractionalBandGeometry`, `BenjaminiSchramm_FractionalSlabGeometry`, `BenjaminiSchramm_FreshSlabConcatenation`, `BenjaminiSchramm_GhostCluster`, `BenjaminiSchramm_GhostMomentBound`, `BenjaminiSchramm_GhostTiltedTransport`, `BenjaminiSchramm_HalfspaceProfileBootstrap`, `BenjaminiSchramm_LayerFirstMoments`, `BenjaminiSchramm_LayerFrontierExpectation`, `BenjaminiSchramm_LayerFrontierGeometry`, `BenjaminiSchramm_LayerMaximumDecomposition`, `BenjaminiSchramm_MixedHeightMoment`, `BenjaminiSchramm_ModularSlabs`, `BenjaminiSchramm_NormalizedHalfspace`, `BenjaminiSchramm_NormalizedLayerTransport`, `BenjaminiSchramm_OrbitHeightComparison`, `BenjaminiSchramm_OrbitNeighborChain`, `BenjaminiSchramm_OrbitNormalization`, `BenjaminiSchramm_OrbitTransport`, `BenjaminiSchramm_PairedSprinkling`, `BenjaminiSchramm_PeakBandProbability`, `BenjaminiSchramm_PeakBandTransport`, `BenjaminiSchramm_PeakConditionalLayers`, `BenjaminiSchramm_PeakCorrelationAveraging`, `BenjaminiSchramm_PeakHalfspaceGeometry`, `BenjaminiSchramm_PeakLayerCost`, `BenjaminiSchramm_PeakOrbitComparison`, `BenjaminiSchramm_PeakSprinklingCell`, `BenjaminiSchramm_PeakSurgeryProbability`, `BenjaminiSchramm_RootTiltedGhost`, `BenjaminiSchramm_SlabFractionalProfileShift`, `BenjaminiSchramm_SusceptibilityDerivative`, `BenjaminiSchramm_TiltedGhost`, `BenjaminiSchramm_TiltedGhostSusceptibility`, `BenjaminiSchramm_TiltedHit`, `BenjaminiSchramm_TiltedSusceptibility`, `BenjaminiSchramm_UpwardFrontierProbability`, `BenjaminiSchramm_WeightedGhostIncidence`, `BenjaminiSchramm_WeightedPeakSlabComparison`, `CriticalPercolation_Classification_AlgebraicDescent`, `CriticalPercolation_Classification_FaithfulOrbitalModel`, `CriticalPercolation_Classification_StructuredCoordinates`, `CriticalPercolation_Clusters_ClusterNumber`, `CriticalPercolation_Clusters_ClusterObject`, `CriticalPercolation_Clusters_ClusterTail`, `CriticalPercolation_Clusters_ClusterUpdate`, `CriticalPercolation_Clusters_Earlier`, `CriticalPercolation_Clusters_ExpectedCluster`, `CriticalPercolation_Clusters_FiniteClusterCover`, `CriticalPercolation_Clusters_ForcedDisconnectContinuity`, `CriticalPercolation_Clusters_HitOthers`, `CriticalPercolation_Clusters_InfiniteUniqueness`, `CriticalPercolation_Clusters_InfiniteUniquenessGeometry`, `CriticalPercolation_Criticality_BalancedCycles`, `CriticalPercolation_Criticality_BandScale`, `CriticalPercolation_Criticality_BlockIndependence`, `CriticalPercolation_Criticality_ComponentCritical`, `CriticalPercolation_Criticality_ContractingDomains`, `CriticalPercolation_Criticality_CylinderApproximation`, `CriticalPercolation_Criticality_DescendingFan`, `CriticalPercolation_Criticality_DirectionalTail`, `CriticalPercolation_Criticality_FiniteInterpolation`, `CriticalPercolation_Criticality_FiniteSeedTree`, `CriticalPercolation_Criticality_FiniteSusceptibility`, `CriticalPercolation_Criticality_GrowthAlternatives`, `CriticalPercolation_Criticality_HeightCuts`, `CriticalPercolation_Criticality_InvariantFiniteSets`, `CriticalPercolation_Criticality_LayerCounting`, `CriticalPercolation_Criticality_MainResidualBoundary`, `CriticalPercolation_Criticality_NestedLayerBlock`, `CriticalPercolation_Criticality_OpenRay`, `CriticalPercolation_Criticality_RestrictedSeed`, `CriticalPercolation_Criticality_ReverseReference`, `CriticalPercolation_Criticality_SquareBoundary`, `CriticalPercolation_Criticality_SubexponentialVolumes`, `CriticalPercolation_Criticality_WitnessEvents`, `CriticalPercolation_Entropy_BinaryConfiguration`, `CriticalPercolation_Entropy_BinaryCosts`, `CriticalPercolation_Entropy_BinaryDescriptor`, `CriticalPercolation_Entropy_BinaryEventBound`, `CriticalPercolation_Entropy_BinaryForest`, `CriticalPercolation_Entropy_BinaryInterpolation`, `CriticalPercolation_Entropy_BinaryInverseCost`, `CriticalPercolation_Entropy_BinaryLaw`, `CriticalPercolation_Entropy_BinaryLikelihood`, `CriticalPercolation_Entropy_BinaryMarks`, `CriticalPercolation_Entropy_BinaryOutput`, `CriticalPercolation_Entropy_BinaryOutputEntropy`, `CriticalPercolation_Entropy_BinaryPairs`, `CriticalPercolation_Entropy_BinaryParents`, `CriticalPercolation_Entropy_BinaryRaw`, `CriticalPercolation_Entropy_BinaryReferenceLikelihood`, `CriticalPercolation_Entropy_BinaryReverseKernels`, `CriticalPercolation_Entropy_BinaryReversePrices`, `CriticalPercolation_Entropy_BinaryStages`, `CriticalPercolation_Entropy_BinarySupport`, `CriticalPercolation_Entropy_BinarySwitches`, `CriticalPercolation_Entropy_BinaryTranscript`, `CriticalPercolation_Entropy_BinaryWords`, `CriticalPercolation_Entropy_MarkedBits`, `CriticalPercolation_Entropy_MarkedEntropy`, `CriticalPercolation_Entropy_ReverseGuess`, `CriticalPercolation_Entropy_Uniform01`, `CriticalPercolation_Exploration_AdaptiveReveal`, `CriticalPercolation_Exploration_AncestryForest`, `CriticalPercolation_Exploration_BallIncidence`, `CriticalPercolation_Exploration_BitWeight`, `CriticalPercolation_Exploration_ClosedFresh`, `CriticalPercolation_Exploration_ClosedPivotWeight`, `CriticalPercolation_Exploration_ClusterUsers`, `CriticalPercolation_Exploration_DecisionHistory`, `CriticalPercolation_Exploration_Initial`, `CriticalPercolation_Exploration_Initial2`, `CriticalPercolation_Exploration_LayerExposure`, `CriticalPercolation_Exploration_Node`, `CriticalPercolation_Exploration_OpenFrontierDivergence`, `CriticalPercolation_Exploration_QueryDelta`, `CriticalPercolation_Exploration_QueryTree`, `CriticalPercolation_Exploration_SearchTree`, `CriticalPercolation_Exploration_SequentialExposure`, `CriticalPercolation_Exploration_SliceExploration`, `CriticalPercolation_Exploration_State`, `CriticalPercolation_Gluing_CollarDistance`, `CriticalPercolation_Gluing_ConditionalGluing`, `CriticalPercolation_Gluing_ContactSelection`, `CriticalPercolation_Gluing_ContourSites`, `CriticalPercolation_Gluing_ContourWords`, `CriticalPercolation_Gluing_CorridorNormalization`, `CriticalPercolation_Gluing_CorridorSeparation`, `CriticalPercolation_Gluing_DomainFreshExit`, `CriticalPercolation_Gluing_EllipseMoves`, `CriticalPercolation_Gluing_FreshExitWitness`, `CriticalPercolation_Gluing_FreshTrial`, `CriticalPercolation_Gluing_LevelContactGeometry`, `CriticalPercolation_Gluing_MoveExit`, `CriticalPercolation_Gluing_MoveWitness`, `CriticalPercolation_Gluing_PinnedTest`, `CriticalPercolation_Gluing_RelayGeometry`, `CriticalPercolation_Gluing_RelayMoves`, `CriticalPercolation_Gluing_RelayScales`, `CriticalPercolation_Gluing_SelectedFresh`, `CriticalPercolation_Gluing_SlotContour`, `CriticalPercolation_Gluing_SourceGraph`, `CriticalPercolation_Gluing_StripMoves`, `CriticalPercolation_GraphGeometry_BallCutGeometry`, `CriticalPercolation_GraphGeometry_Column`, `CriticalPercolation_GraphGeometry_ComponentAction`, `CriticalPercolation_GraphGeometry_Connects`, `CriticalPercolation_GraphGeometry_CutEdges`, `CriticalPercolation_GraphGeometry_DeletedTailGeometry`, `CriticalPercolation_GraphGeometry_EllipseExit`, `CriticalPercolation_GraphGeometry_EllipseLinear`, `CriticalPercolation_GraphGeometry_EllipseSeed`, `CriticalPercolation_GraphGeometry_EncounterGeometry`, `CriticalPercolation_GraphGeometry_EraseBond`, `CriticalPercolation_GraphGeometry_FiniteIndexAction`, `CriticalPercolation_GraphGeometry_FiniteInduced`, `CriticalPercolation_GraphGeometry_FullOrbitalStructureTransfer`, `CriticalPercolation_GraphGeometry_GraphAction`, `CriticalPercolation_GraphGeometry_GraphActionCoordinates`, `CriticalPercolation_GraphGeometry_GraphBalls`, `CriticalPercolation_GraphGeometry_HitEvent`, `CriticalPercolation_GraphGeometry_InducedAutomorphism`, `CriticalPercolation_GraphGeometry_IsolateThree`, `CriticalPercolation_GraphGeometry_MapVertices`, `CriticalPercolation_GraphGeometry_MovingStrips`, `CriticalPercolation_GraphGeometry_ObjectKernel`, `CriticalPercolation_GraphGeometry_OpenGraphIso`, `CriticalPercolation_GraphGeometry_OrbitRepresentatives`, `CriticalPercolation_GraphGeometry_OrbitalAction`, `CriticalPercolation_GraphGeometry_OrbitalPower`, `CriticalPercolation_GraphGeometry_OrbitalStructureTransfer`, `CriticalPercolation_GraphGeometry_RestrictVertices`, `CriticalPercolation_GraphGeometry_RestrictedAction`, `CriticalPercolation_GraphGeometry_StripCompactness`, `CriticalPercolation_GraphGeometry_StripLinear`, `CriticalPercolation_GraphGeometry_UniformGeometry`, `CriticalPercolation_GraphGeometry_UpdateKernel`, `CriticalPercolation_GraphGeometry_VertexBall`, `CriticalPercolation_GraphGeometry_WiredEvent`, `CriticalPercolation_GraphTopology_OrbitalNeighborhoods`, `CriticalPercolation_Growth_SuperpolynomialRadius`, `CriticalPercolation_LinearGroups_ClusterMatrix`, `CriticalPercolation_Model`, `CriticalPercolation_Modular_ActionOrbitTransport`, `CriticalPercolation_Modular_CappedDiscrepancy`, `CriticalPercolation_Modular_ClusterDiscrepancy`, `CriticalPercolation_Modular_CriticalHeavyIdentity`, `CriticalPercolation_Modular_DiscrepancyTail`, `CriticalPercolation_Modular_ExpectedIncidenceTransport`, `CriticalPercolation_Modular_GraphModular`, `CriticalPercolation_Modular_HeavyClusterNumber`, `CriticalPercolation_Modular_HeavyFiniteGeometry`, `CriticalPercolation_Modular_HeavyHarris`, `CriticalPercolation_Modular_HeavyPeaks`, `CriticalPercolation_Modular_HeavyThinning`, `CriticalPercolation_Modular_LightClusterNumber`, `CriticalPercolation_Modular_LightSliceFrontier`, `CriticalPercolation_Modular_LightTwoPointDecay`, `CriticalPercolation_Modular_ModularClusterCount`, `CriticalPercolation_Modular_ModularClusterMass`, `CriticalPercolation_Modular_ModularIncidence`, `CriticalPercolation_Modular_ModularLevelGeometry`, `CriticalPercolation_Modular_ModularSuperlevels`, `CriticalPercolation_Modular_NormalizedDiscrepancy`, `CriticalPercolation_Modular_NormalizedIncidenceTransport`, `CriticalPercolation_Modular_ObjectAvoidMass`, `CriticalPercolation_Modular_OrbitalMassTransport`, `CriticalPercolation_Modular_PeakClusters`, `CriticalPercolation_Modular_PeakRatioTransport`, `CriticalPercolation_Modular_PeakReturn`, `CriticalPercolation_Modular_PeakVolumeBand`, `CriticalPercolation_Modular_PushMass`, `CriticalPercolation_Modular_RelativeModular`, `CriticalPercolation_Modular_SignedDiscrepancyContinuity`, `CriticalPercolation_Modular_TiltedTransportENNReal`, `CriticalPercolation_Modular_UnimodularGeometric`, `CriticalPercolation_Modular_Unimodularity`, `CriticalPercolation_Modular_WeightedDiscrepancy`, `CriticalPercolation_Modular_WeightedDiscrepancyLimit`, `CriticalPercolation_Modular_WeightedPeakTransport`, `CriticalPercolation_ProductMeasure_BitMeasure`, `CriticalPercolation_ProductMeasure_ContourProbability`, `CriticalPercolation_ProductMeasure_Delta`, `CriticalPercolation_ProductMeasure_Density`, `CriticalPercolation_ProductMeasure_Distribution`, `CriticalPercolation_ProductMeasure_FiniteInterpolationMeasure`, `CriticalPercolation_ProductMeasure_FiniteOpenWitness`, `CriticalPercolation_ProductMeasure_FiniteProductPin`, `CriticalPercolation_ProductMeasure_LayerExpectation`, `CriticalPercolation_ProductMeasure_LevelContactMeasurability`, `CriticalPercolation_ProductMeasure_MonotoneBernoulli`, `CriticalPercolation_ProductMeasure_Prob`, `CriticalPercolation_ProductMeasure_ProductConditioning`, `CriticalPercolation_ProductMeasure_RelayProbability`, `CriticalPercolation_ProductMeasure_TailProduct`, `UnimodularPercolation_Clusters_KernelMoments`, `UnimodularPercolation_Clusters_LargeContacts`, `UnimodularPercolation_Criticality_Sharpness`, `UnimodularPercolation_Criticality_Susceptibility`, `UnimodularPercolation_Escape_Labels`, `UnimodularPercolation_Exploration_Goodness`, `UnimodularPercolation_Exploration_Marked`, `UnimodularPercolation_Exploration_Moments`, `UnimodularPercolation_Graph_Basic`, `UnimodularPercolation_Graph_Paths`, `UnimodularPercolation_Kernel_Covariance`, `UnimodularPercolation_Kernel_RussoRows`, `UnimodularPercolation_Kernel_Spectral`, `UnimodularPercolation_Kernel_Sprinkling`, `UnimodularPercolation_ProductMeasure_Association`, `UnimodularPercolation_Splicing_EndpointMoments`, `UnimodularPercolation_Splicing_GapCodes`, `UnimodularPercolation_Splicing_Geometry`, `UnimodularPercolation_Splicing_MomentBounds`, `UnimodularPercolation_Splicing_ReferenceLaws`, `UnimodularPercolation_Splicing_Replay`, `UnimodularPercolation_Subdivision_Coupling`, `UnimodularPercolation_Subdivision_Graph`, `UnimodularPercolation_Transport_EndpointKernels`, `UnimodularPercolation_Transport_TrajectoryMass`.
--
--   **Imports.** It imports the published bundle `Def_BenjaminiSchramm`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ078B002`; the statements `OAI_CriticalPercolation_BinaryLaw_conditioned_reference_density_le`, `OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le_bs`, `OAI_CriticalPercolation_BinaryLaw_selected_density_le`, `OAI.CriticalPercolation.BinaryLaw.selected_density_le_bs`, `OAI_CriticalPercolation_BondGraph_CombinatoriallyUnimodular_exponential_critical_null`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular.exponential_critical_null_bs`, `OAI_CriticalPercolation_BondGraph_UnimodularRoot_subcritical_adjacent_bound`, `OAI.CriticalPercolation.BondGraph.UnimodularRoot.subcritical_adjacent_bound_bs`, `OAI_CriticalPercolation_BondGraph_approximate_moves_contradiction`, `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction_bs`, `OAI_CriticalPercolation_BondGraph_atMostOneHeavy_critical_ae`, `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae_bs`, `OAI_CriticalPercolation_BondGraph_coordinate_pinned_corridor_failure`, `OAI.CriticalPercolation.BondGraph.coordinate_pinned_corridor_failure_bs`, `OAI_CriticalPercolation_BondGraph_critical_null_of_action_coordinates`, `OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates_bs`, `OAI_CriticalPercolation_BondGraph_critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs`, `OAI_CriticalPercolation_BondGraph_critical_strip_null`, `OAI.CriticalPercolation.BondGraph.critical_strip_null_bs`, `OAI_CriticalPercolation_BondGraph_ellipse_critical_contradiction`, `OAI.CriticalPercolation.BondGraph.ellipse_critical_contradiction_bs`, `OAI_CriticalPercolation_BondGraph_eventually_no_superpolynomial_band`, `OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs`, `OAI_CriticalPercolation_BondGraph_expected_heavy_normalizedDiscrepancy_bound`, `OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound_bs`, `OAI_CriticalPercolation_BondGraph_fresh_contact_transfer`, `OAI.CriticalPercolation.BondGraph.fresh_contact_transfer_bs`, `OAI_CriticalPercolation_BondGraph_halfspace_fractional_profile_bootstrap`, `OAI.CriticalPercolation.BondGraph.halfspace_fractional_profile_bootstrap_bs`, `OAI_CriticalPercolation_BondGraph_main_failure_topological_classification_counterexample`, `OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs`, `OAI_CriticalPercolation_BondGraph_main_light_or_sparse_polynomial_boundary`, `OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs`, `OAI_CriticalPercolation_BondGraph_nonunimodular_critical_mass_finite_ae`, `OAI.CriticalPercolation.BondGraph.nonunimodular_critical_mass_finite_ae_bs`, `OAI_CriticalPercolation_BondGraph_nonunimodular_no_percolation_at_criticality`, `OAI.CriticalPercolation.BondGraph.nonunimodular_no_percolation_at_criticality_bs`, `OAI_CriticalPercolation_BondGraph_normalized_crossing_exponent_approximation`, `OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation_bs`, `OAI_CriticalPercolation_BondGraph_original_root_corridor_miss`, `OAI.CriticalPercolation.BondGraph.original_root_corridor_miss_bs`, `OAI_CriticalPercolation_BondGraph_peak_sprinkling_eventual_survival`, `OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival_bs`, `OAI_CriticalPercolation_BondGraph_restricted_interpolation_measure`, `OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_bs`, `OAI_CriticalPercolation_BondGraph_subcritical_normalized_layer_rate`, `OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate_bs`, `OAI_CriticalPercolation_BondGraph_subcritical_seedExpectation_bound`, `OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound_bs`, `OAI_CriticalPercolation_BondGraph_subexponential_adjacent_bound`, `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound_bs`, `OAI_CriticalPercolation_BondGraph_uniform_lower_nestedLayer_blocks`, `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks_bs`, `OAI_CriticalPercolation_BondGraph_uniform_rooted_probability`, `OAI.CriticalPercolation.BondGraph.uniform_rooted_probability_bs`, `OAI_CriticalPercolation_BondGraph_unique_cluster_direction_unbounded_ae`, `OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs`, `OAI_CriticalPercolation_BondGraph_upward_ceiling_profile`, `OAI.CriticalPercolation.BondGraph.upward_ceiling_profile_bs`, `OAI_CriticalPercolation_BondGraph_upward_fractional_slab_profile`, `OAI.CriticalPercolation.BondGraph.upward_fractional_slab_profile_bs`, `OAI_CriticalPercolation_Sharpness_critical_null_of_unique`, `OAI.CriticalPercolation.Sharpness.critical_null_of_unique_bs`, `OAI_CriticalPercolation_nilpotent_descent` and `OAI.CriticalPercolation.nilpotent_descent_bs`; the proofs of `OAI_CriticalPercolation_BondGraph_atMostOneHeavy_critical_ae`, `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae_bs`, `OAI_CriticalPercolation_BondGraph_coordinate_pinned_corridor_failure`, `OAI.CriticalPercolation.BondGraph.coordinate_pinned_corridor_failure_bs`, `OAI_CriticalPercolation_BondGraph_critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs`, `OAI_CriticalPercolation_BondGraph_ellipse_critical_contradiction`, `OAI.CriticalPercolation.BondGraph.ellipse_critical_contradiction_bs`, `OAI_CriticalPercolation_BondGraph_original_root_corridor_miss`, `OAI.CriticalPercolation.BondGraph.original_root_corridor_miss_bs`, `OAI_CriticalPercolation_BondGraph_unique_cluster_direction_unbounded_ae`, `OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs`, `OAI_CriticalPercolation_HarmonicAnalysis_WordGeometry_exists_infinite_finiteDimensional_linear_image`, `OAI.CriticalPercolation.HarmonicAnalysis.WordGeometry.exists_infinite_finiteDimensional_linear_image_bs`, `OAI_CriticalPercolation_nilpotent_descent`, `OAI.CriticalPercolation.nilpotent_descent_bs` and `OAI.Percolation.BenjaminiSchramm.critical_laws`.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_BenjaminiSchramm

section
-- module Solutions.OAIQ078_BS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def density (w : E → A → ℝ) (ω : E → A) : ℝ := ∏ e, w e (ω e)

noncomputable def expect (w : E → A → ℝ) (f : (E → A) → ℝ) : ℝ := by
  classical
  exact ∑ ω, density w ω * f ω

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BitMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BernoulliProduct

noncomputable def bitMeasure (p : unitInterval) : Measure Prop :=
  unitInterval.toNNReal p • Measure.dirac True +
    unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False

instance bitMeasure_probability (p : unitInterval) : IsProbabilityMeasure (bitMeasure p) := by
  constructor
  simp [bitMeasure]

noncomputable def bitWeight (p : unitInterval) (b : Prop) : ℝ :=
  if b then p else 1-p

variable {E : Type*}

noncomputable def law (q : E → unitInterval) : Measure (Set E) :=
  Measure.map MeasurableEquiv.setOfPred (Measure.infinitePi fun e => bitMeasure (q e))

instance law_probability (q : E → unitInterval) : IsProbabilityMeasure (law q) := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_TailProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

abbrev coordinateSigma (e : E) : MeasurableSpace (Set E) :=
  MeasurableSpace.comap (fun ω : Set E => e ∈ ω) inferInstance

abbrev blockSigma (S : Set E) : MeasurableSpace (Set E) := ⨆ e ∈ S, coordinateSigma e

lemma coordinateSigma_le (e : E) : coordinateSigma e ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  (measurable_set_mem e).comap_le

lemma blockSigma_le (S : Set E) : blockSigma S ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  iSup₂_le fun e _ => coordinateSigma_le e

def forceOn (S : Set E) (σ ω : Set E) : Set E := fun e => if e ∈ S then e ∈ σ else e ∈ ω

lemma measurable_forceOn_block (S σ : Set E) :
    @Measurable (Set E) (Set E) (blockSigma Sᶜ) inferInstance (forceOn S σ) := by
  refine (@measurable_pi_iff (Set E) E (fun _ => Prop) (blockSigma Sᶜ)
    (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e ∈ S
  · simpa only [forceOn, ite_eq_left he] using
      (@measurable_const Prop (Set E) inferInstance (blockSigma Sᶜ) (e ∈ σ))
  · have hm : @Measurable (Set E) Prop (coordinateSigma e) inferInstance
        (fun ω => e ∈ ω) := measurable_iff_comap_le.mpr le_rfl
    have hl : coordinateSigma e ≤ blockSigma Sᶜ := le_iSup_of_le e (le_iSup_of_le he le_rfl)
    simpa only [forceOn, ite_eq_right he] using hm.mono hl le_rfl

lemma measurable_forceOn (S σ : Set E) : Measurable (forceOn S σ) :=
  (measurable_forceOn_block S σ).mono (blockSigma_le Sᶜ) le_rfl

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteProductPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def pin (w : E → A → ℝ) (e : E) (b : A) : E → A → ℝ :=
  Function.update w e (fun a => if a = b then 1 else 0)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def distribution {B : Type*} [DecidableEq B]
    (w : E → A → ℝ) (φ : (E → A) → B) (b : B) : ℝ :=
  expect w (fun ω => if φ ω = b then 1 else 0)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def prob (w : E → Prop → ℝ) (P : Set E → Prop) : ℝ :=
  expect w (fun ω => if P ω then 1 else 0)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Delta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def delta (w : E → Prop → ℝ) (F : Set E → Prop) (e : E) : ℝ :=
  prob (pin w e True) F - prob (pin w e False) F

def openPivot (F : Set E → Prop) (e : E) (ω : Set E) : Prop :=
  ω e ∧ F ω ∧ ¬F (Function.update ω e False)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProductConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

@[simp] lemma mem_forceOn (S σ ω : Set E) (e : E) :
    e∈forceOn S σ ω ↔ if e∈S then e∈σ else e∈ω := Iff.rfl

lemma measurable_forceOn_joint_block (S : Set E) :
    @Measurable (Set E × Set E) (Set E)
      ((blockSigma S).prod inferInstance) inferInstance
      (fun z => forceOn S z.1 z.2) := by
  refine (@measurable_pi_iff (Set E × Set E) E (fun _ => Prop)
    ((blockSigma S).prod inferInstance) (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e∈S
  · have hm : @Measurable (Set E) Prop (blockSigma S) inferInstance
        (fun σ => e∈σ) := by
      apply measurable_iff_comap_le.mpr
      exact le_iSup_of_le e (le_iSup_of_le he le_rfl)
    simpa only [forceOn,ite_eq_left he,Function.comp_def] using hm.comp measurable_fst
  · simpa only [forceOn,ite_eq_right he,Function.comp_def] using (measurable_set_mem e).comp measurable_snd

def pinnedParameters (q : E → unitInterval) (S σ : Set E) : E → unitInterval :=
  fun e => if e∈S then if e∈σ then 1 else 0 else q e

def blockProbability (q : E → unitInterval) (S : Set E) (A : Set (Set E))
    (σ : Set E) : ℝ≥0∞ := law q ((forceOn S σ) ⁻¹' A)

lemma blockProbability_eq_lintegral (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (σ : Set E) :
    blockProbability q S A σ=∫⁻ ω, A.indicator (1 : Set E → ℝ≥0∞) (forceOn S σ ω) ∂law q := by
  unfold blockProbability
  rw [← lintegral_indicator_one (hA.preimage (measurable_forceOn S σ))]
  rfl

lemma measurable_blockProbability (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance (blockProbability q S A) := by
  have hI : @Measurable (Set E × Set E) ℝ≥0∞
      ((blockSigma S).prod Set.instMeasurableSpace) inferInstance
      (fun z => A.indicator (1 : Set E → ℝ≥0∞) (forceOn S z.1 z.2)) :=
    @Measurable.comp (Set E × Set E) (Set E) ℝ≥0∞
      ((blockSigma S).prod Set.instMeasurableSpace) Set.instMeasurableSpace inferInstance
      _ _ (measurable_const.indicator hA) (measurable_forceOn_joint_block S)
  have hm := @Measurable.lintegral_prod_right' (Set E) (Set E)
    (blockSigma S) Set.instMeasurableSpace (law q) inferInstance _ hI
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext σ
  exact blockProbability_eq_lintegral q S A hA σ

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}



section Deterministic
variable (G : BondGraph V E) (ω : Set E)

@[simp] theorem conn_refl (x : V) : Conn G ω x x :=
  Relation.ReflTransGen.refl

@[simp] theorem mem_cluster_self (x : V) : x ∈ cluster G ω x := conn_refl G ω x

@[simp] theorem conn_empty_iff (x y : V) : Conn G ∅ x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ he _ => rcases he with ⟨e, he, _⟩; exact he.elim
  · rintro rfl
    exact conn_refl G ∅ _

@[simp] theorem cluster_empty (x : V) : cluster G ∅ x = {x} := by
  ext y
  simp [cluster, eq_comm]

@[simp] theorem infiniteClusters_empty : infiniteClusters G ∅ = ∅ := by
  ext C
  simp only [infiniteClusters, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_and, not_exists]
  intro h x hx
  subst C
  simp at h

end Deterministic

section Probability
variable (G : BondGraph V E)

instance law_isProbabilityMeasure (p : unitInterval) :
    IsProbabilityMeasure (law p : Measure (Set E)) := by
  dsimp [law]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

@[simp] theorem law_zero : (law 0 : Measure (Set E)) = Measure.dirac ∅ := by
  simp [law]

@[simp] theorem law_one : (law 1 : Measure (Set E)) = Measure.dirac Set.univ := by
  simp [law]

@[simp] theorem twoPoint_self (p : unitInterval) (x : V) : twoPoint G p x x = 1 := by
  simp [twoPoint]

@[simp] theorem twoPoint_zero [Countable E] [DecidableEq V] (x y : V) :
    twoPoint G 0 x y = if x = y then 1 else 0 := by
  rw [twoPoint, law_zero, Measure.dirac_apply]
  by_cases h : x = y
  · simp [h]
  · rw [Set.indicator_of_notMem (by simpa using h)]
    simp [h]

end Probability

section Countability

 
theorem finite_neighbors {G : BondGraph V E} (hG : LocallyFinite G) (x : V) :
    {y | Adj G x y}.Finite := by
  classical
  have hends (e : E) : {y | y ∈ G e}.Finite := by
    apply (G e).toFinset.finite_toSet.subset
    intro y hy
    exact Sym2.mem_toFinset.mpr hy
  have hs : (⋃ e ∈ {e | x ∈ G e}, {y | y ∈ G e}).Finite :=
    (hG x).biUnion (fun e _ => hends e)
  apply hs.subset
  rintro y ⟨e, he⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨e, he ▸ by simp, he ▸ by simp⟩


end Countability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Automorphisms
attribute [local instance] Classical.propDecidable

theorem isAut_symm (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) : IsAut G a.symm b.symm := by
  intro e
  have hh := congrArg (Sym2.map a.symm) (h (b.symm e))
  simpa only [Equiv.apply_symm_apply, Sym2.map_map, Equiv.symm_comp_self,
    Sym2.map_id', id_eq] using hh.symm

theorem conn_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {ω : Set E} {x y : V} (hc : Conn G ω x y) :
    Conn G (b '' ω) (a x) (a y) := by
  induction hc with
  | refl => exact conn_refl G _ _
  | @tail v w hvw hed ih =>
    obtain ⟨e, he, hGe⟩ := hed
    exact ih.tail ⟨b e, Set.mem_image_of_mem _ he, by rw [h e, hGe, Sym2.map_mk]⟩

theorem conn_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (ω : Set E) (x y : V) :
    Conn G (b ⁻¹' ω) x y ↔ Conn G ω (a x) (a y) := by
  constructor
  · intro hc
    simpa only [Set.image_preimage_eq _ b.surjective] using conn_aut G h hc
  · intro hc
    have he : b.symm '' ω = b ⁻¹' ω := by
      ext e
      simp
    simpa only [Equiv.symm_apply_apply, he] using
      conn_aut G (isAut_symm G h) hc

end Automorphisms

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section BondPaths
attribute [local instance] Classical.propDecidable

 
inductive Along (G : BondGraph V E) : V → List E → V → Prop
  | nil (x : V) : Along G x [] x
  | cons {x z y : V} {l : List E} (e : E) (he : G e = s(x,z))
      (tail : Along G z l y) : Along G x (e :: l) y

 theorem Along.conn {G : BondGraph V E} {x y : V} {l : List E} (h : Along G x l y)
    {ω : Set E} (ho : ∀ e ∈ l, e ∈ ω) : Conn G ω x y := by
  induction h with
  | nil => exact conn_refl G ω _
  | @cons x z y l e he ht ih =>
    exact (Relation.ReflTransGen.single ⟨e, ho e (by simp), he⟩).trans
      (ih (fun e' he' => ho e' (by simp [he'])))

 theorem conn_iff_reachable (G : BondGraph V E) (ω : Set E) (x y : V) :
    Conn G ω x y ↔ (openSimpleGraph G ω).Reachable x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨.nil⟩
    | @tail z y h hy ih =>
      obtain ⟨w⟩ := ih
      by_cases hzy : z = y
      · subst y; exact ⟨w⟩
      · exact ⟨w.concat ⟨hzy, hy⟩⟩
  · rintro ⟨w⟩
    induction w with
    | nil => exact conn_refl G ω _
    | @cons x z y hadj w ih =>
      exact (Relation.ReflTransGen.single hadj.2).trans ih

 theorem walk_lift_bonds (G : BondGraph V E) (ω : Set E) {x y : V}
    (w : (openSimpleGraph G ω).Walk x y) :
    ∃ l : List E, Along G x l y ∧ l.map G = w.edges ∧ ∀ e ∈ l, e ∈ ω := by
  induction w with
  | nil => exact ⟨[], .nil _, rfl, by simp⟩
  | @cons x z y hadj w ih =>
    obtain ⟨e, he, heq⟩ := hadj.2
    obtain ⟨l, hl, hmap, hopen⟩ := ih
    refine ⟨e :: l, .cons e heq hl, ?_, ?_⟩
    · simp [hmap, heq]
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact he
      · exact hopen e' he'

 
 theorem conn_exists_bond_trail (G : BondGraph V E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    ∃ l : List E, Along G x l y ∧ l.Nodup ∧ ∀ e ∈ l, e ∈ ω := by
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp h
  obtain ⟨l, hl, hmap, hopen⟩ := walk_lift_bonds G ω (w.toPath : (openSimpleGraph G ω).Walk x y)
  refine ⟨l, hl, ?_, hopen⟩
  apply List.Nodup.of_map (f := G)
  rw [hmap]
  exact w.toPath.property.isTrail.edges_nodup

end BondPaths

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Sprinkling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SprinklingLaw
attribute [local instance] Classical.propDecidable

 def pairParameter (p a : unitInterval) (b : Bool) : unitInterval := if b then p else a

end SprinklingLaw

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


def internalEdges (G : BondGraph V E) (S : Set V) : Set E :=
  {e | ∀ x ∈ G e, x ∈ S}

@[simp] theorem mem_internalEdges_of_ends (G : BondGraph V E) (S : Set V)
    (e : E) (a b : V) (he : G e = s(a,b)) :
    e ∈ internalEdges G S ↔ a ∈ S ∧ b ∈ S := by
  simp [internalEdges, he]

 
def unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E) : Set V :=
  {x | ∀ y, Conn G ω x y → y ∈ Λ}

theorem unexposed_subset (G : BondGraph V E) (Λ : Set V) (ω : Set E) :
    unexposed G Λ ω ⊆ Λ := fun x hx => hx x (conn_refl G ω x)

attribute [local instance] Classical.decEq


noncomputable def unexposedRegion (G : BondGraph V E) (Λ : Finset V) (ω : Set E) : Finset V :=
  ((Set.toFinite (Λ : Set V)).subset (unexposed_subset G (Λ : Set V) ω)).toFinset

@[simp] theorem coe_unexposedRegion (G : BondGraph V E) (Λ : Finset V) (ω : Set E) :
    (unexposedRegion G Λ ω : Set V) = unexposed G (Λ : Set V) ω := by
  simp [unexposedRegion]

end ExteriorExposure

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology


noncomputable def incidentSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) : Finset E := Λ.biUnion (fun x => (hloc x).toFinset)

@[simp] theorem mem_incidentSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (e : E) : e ∈ incidentSupport G hloc Λ ↔ ∃ x ∈ Λ, x ∈ G e := by
  simp [incidentSupport]

end SharpnessBridge

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq


def CutExists (G : BondGraph V E) (S : Set V) (e : E) : Prop :=
  ∃ a b, G e = s(a,b) ∧ a ∈ S ∧ b ∉ S

end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Marked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked decision trees, graph searches and pivotal geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedFirstMoment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


noncomputable def markedOpenPivotals (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) : Finset E :=
  Q.filter fun e => e ∈ ω ∧ (∃ y ∈ m, Conn G (ω : Set E) x y) ∧
      ¬ ∃ y ∈ m, Conn G (ω.erase e : Set E) x y


end MarkedFirstMoment

section PivotalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
def MarkedEvent (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V) : Prop :=
  ∃ y ∈ m, Conn G ω x y

 
def OpenMarkedPivotal (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    (e : E) : Prop :=
  e ∈ ω ∧ MarkedEvent G ω m x ∧ ¬MarkedEvent G (ω \ {e}) m x


theorem cluster_finite_of_finite_edges (G : BondGraph V E) {ω : Set E}
    (hω : ω.Finite) (x : V) : (cluster G ω x).Finite := by
  let F : Finset V := insert x (hω.toFinset.biUnion fun e => (G e).toFinset)
  apply F.finite_toSet.subset
  intro y hxy
  induction hxy with
  | refl => exact Finset.mem_insert_self x _
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨e,hω.mem_toFinset.mpr he,by simp [heq]⟩


end PivotalGeometry

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive marked moments and exponential estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedRecursion
attribute [local instance] Classical.propDecidable Classical.decEq


@[simp] theorem mem_markedOpenPivotals (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) (e : E) :
    e ∈ markedOpenPivotals G Q x ω m ↔ e ∈ Q ∧ OpenMarkedPivotal G ω m x e := by
  simp only [markedOpenPivotals,Finset.mem_filter,OpenMarkedPivotal,MarkedEvent,Finset.coe_erase,
    Finset.mem_coe]

 
noncomputable def markedMomentValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if MarkedEvent G ω m x then ((markedOpenPivotals G Q x ω m).card.choose i : ℝ) else 0


@[simp] theorem markedMomentValue_zero (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x 0 ω m = if MarkedEvent G ω m x then 1 else 0 := by
  simp only [markedMomentValue,Nat.choose_zero_right,Nat.cast_one]

@[simp] theorem markedMomentValue_one (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x 1 ω m = ((markedOpenPivotals G Q x ω m).card : ℝ) := by
  by_cases h : MarkedEvent G ω m x
  · simp [markedMomentValue,h]
  · have he : markedOpenPivotals G Q x ω m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact h ((mem_markedOpenPivotals G Q x ω m e).mp he).2.2.1
    simp [markedMomentValue,h,he]


noncomputable def exteriorBonds (G : BondGraph V E) (Q : Finset E) (W : Set V) : Finset E :=
  Q.filter fun e => e ∈ internalEdges G Wᶜ

@[simp] theorem coe_exteriorBonds (G : BondGraph V E) (Q : Finset E) (W : Set V) :
    (exteriorBonds G Q W : Set E) = (Q : Set E) ∩ internalEdges G Wᶜ := by
  ext e; simp [exteriorBonds]

end MarkedRecursion

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

noncomputable def finiteRootComponent (G : BondGraph V E) (ω : Finset E) (x : V) : Finset V :=
  (cluster_finite_of_finite_edges G ω.finite_toSet x).toFinset

omit [Nonempty V] in
@[simp]
theorem coe_finiteRootComponent (G : BondGraph V E) (ω : Finset E) (x : V) :
    (finiteRootComponent G ω x : Set V) = cluster G ω x := by simp [finiteRootComponent]

end PointwiseRecursion

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Goodness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteCappedRadius
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def pairOpenPivotals (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) : Finset E :=
  Q.filter fun e => e ∈ ω ∧ Conn G (ω : Set E) x y ∧ ¬Conn G (ω.erase e : Set E) x y


end FiniteCappedRadius

section PruningGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def internalBonds (G : BondGraph V E) (ω : Finset E) (W : Set V) : Finset E :=
  ω.filter fun e => e ∈ internalEdges G W

@[simp] theorem coe_internalBonds (G : BondGraph V E) (ω : Finset E) (W : Set V) :
    (internalBonds G ω W : Set E) = (ω : Set E) ∩ internalEdges G W := by
  ext e; simp [internalBonds]


end PruningGeometry

section GoodnessGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem mem_pairOpenPivotals (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) (e : E) : e ∈ pairOpenPivotals G Q x y ω ↔
      e ∈ Q ∧ OpenMarkedPivotal G (ω : Set E) {y} x e := by
  simp only [pairOpenPivotals,Finset.mem_filter,OpenMarkedPivotal,MarkedEvent,
    Set.mem_singleton_iff,exists_eq_left,Finset.coe_erase,Finset.mem_coe]


noncomputable def incidentBonds (G : BondGraph V E) (Q : Finset E) (W : Finset V) : Finset E :=
  W.biUnion fun v => Q.filter fun e => v ∈ G e

@[simp] theorem mem_incidentBonds (G : BondGraph V E) (Q : Finset E) (W : Finset V) (e : E) :
    e ∈ incidentBonds G Q W ↔ e ∈ Q ∧ ∃ v ∈ W, v ∈ G e := by
  simp only [incidentBonds,Finset.mem_biUnion,Finset.mem_filter]
  aesop

end GoodnessGeometry

section InfiniteGoodness
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def pivotalDistance (G : BondGraph V E) (ω : Set E) (a b : V) : ℕ :=
  {e | OpenMarkedPivotal G ω {b} a e}.ncard

 
def contactSet (G : BondGraph V E) (ω : Set E) (W : Set V) : Set E :=
  {e | e ∈ ω ∧ CutExists G W e}


end InfiniteGoodness

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


noncomputable def neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Finset V := (finite_neighbors hloc x).toFinset

@[simp] theorem mem_neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x y : V) :
    y ∈ neighbors G hloc x ↔ Adj G x y := by simp [neighbors]

noncomputable def finiteAdjPairs (G : BondGraph V E) (K : Finset V) : Finset (V × V) :=
  (K ×ˢ K).filter (fun e => Adj G e.1 e.2)

@[simp] theorem mem_finiteAdjPairs (G : BondGraph V E) (K : Finset V) (e : V × V) :
    e ∈ finiteAdjPairs G K ↔ e.1 ∈ K ∧ e.2 ∈ K ∧ Adj G e.1 e.2 := by
  simp [finiteAdjPairs,and_assoc]

theorem adj_symm (G : BondGraph V E) {x y : V} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,he.trans (Sym2.eq_swap)⟩

end IsoperimetricEnergy

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical parameters and the geometry, selection and traces of splices. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

def exchangeOn (mask ω η : Set E) : Set E := (ω \ mask) ∪ (η ∩ mask)

@[simp] theorem mem_exchangeOn {mask ω η : Set E} {e : E} :
    e ∈ exchangeOn mask ω η ↔ if e ∈ mask then e ∈ η else e ∈ ω := by
  by_cases h : e ∈ mask <;> simp [exchangeOn,h]



def spliceMask (G : BondGraph V E) (S B : Set V) (e : E) : Set E :=
  insert e {f | (∃ b ∈ B, b ∈ G f) ∧ f ∈ internalEdges G Sᶜ}

def spliceField (G : BondGraph V E) (S B : Set V) (e : E) (ω η : Set E) : Set E :=
  exchangeOn (spliceMask G S B e) ω η

end SpliceGeometry

section FiniteExchange
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteExchange (M ω η : Finset E) : Finset E := (ω \ M) ∪ (η ∩ M)

@[simp] theorem coe_finiteExchange (M ω η : Finset E) :
    (finiteExchange M ω η : Set E) = exchangeOn (M:Set E) (ω:Set E) (η:Set E) := by
  simp only [finiteExchange,exchangeOn,Finset.coe_union,Finset.coe_sdiff,Finset.coe_inter]

end FiniteExchange

section SpliceTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

inductive SpliceTrace (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k : ℕ) :
    ℕ → Set E → List (ℕ × E) → Set E → Prop
  | stop (j : ℕ) (ω : Set E) (hstop : y k ∈ cluster G ω x) :
      SpliceTrace G x η y k j ω [] ω
  | step (j i : ℕ) (ω : Set E) (e : E) (a b : V) (rest : List (ℕ × E)) (ωf : Set E)
      (hnot : y k ∉ cluster G ω x) (hji : j < i) (hik : i ≤ k)
      (hmax : ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) (cluster G ω x))
      (hy : y i ∉ cluster G ω x) (he : e ∈ η i) (hab : G e = s(a,b))
      (ha : a ∈ cluster G ω x)
      (hb : b ∈ cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))
      (htail : SpliceTrace G x η y k i
        (spliceField G (cluster G ω x)
          (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i)) rest ωf) :
      SpliceTrace G x η y k j ω ((i,e)::rest) ωf



end SpliceTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_GapCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gap Codes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceExecution
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev SpliceState (E : Type v) := Set E × (ℕ → Set E)

 

def exchangeState (mask : Set E) (i : ℕ) (s : SpliceState E) : SpliceState E :=
  (exchangeOn mask s.1 (s.2 i), Function.update s.2 i (exchangeOn mask (s.2 i) s.1))

@[simp] theorem exchangeState_first (mask : Set E) (i : ℕ) (s : SpliceState E) :
    (exchangeState mask i s).1 = exchangeOn mask s.1 (s.2 i) := rfl

@[simp] theorem exchangeState_at (mask : Set E) (i : ℕ) (s : SpliceState E) :
    (exchangeState mask i s).2 i = exchangeOn mask (s.2 i) s.1 := by
  simp [exchangeState]

theorem exchangeState_away (mask : Set E) (i l : ℕ) (s : SpliceState E) (hli : l ≠ i) :
    (exchangeState mask i s).2 l = s.2 l := by
  simp [exchangeState, Function.update_of_ne hli]



def ValidSpliceStep (G : BondGraph V E) (x : V) (s : SpliceState E)
    (q : ℕ × E) (s' : SpliceState E) : Prop :=
  ∃ y a b,
    y ∉ cluster G s.1 x ∧ q.2 ∈ s.2 q.1 ∧ G q.2 = s(a,b) ∧
    a ∈ cluster G s.1 x ∧
    b ∈ cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y ∧
    s' = exchangeState
      (spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2) q.1 s


inductive SpliceExecution (G : BondGraph V E) (x : V) :
    SpliceState E → List (ℕ × E) → SpliceState E → Prop
  | nil (s) : SpliceExecution G x s [] s
  | cons (s s' s'') (q qs)
      (hstep : ValidSpliceStep G x s q s')
      (hrest : SpliceExecution G x s' qs s'') : SpliceExecution G x s (q::qs) s''


end SpliceExecution

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeCode
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem pivotal_mem_trail (G : BondGraph V E) (ω : Set E) (x z : V)
    (l : List E) (hl : Along G x l z) (hopen : ∀ e ∈ l, e ∈ ω)
    {e : E} (he : OpenMarkedPivotal G ω {z} x e) : e ∈ l := by
  by_contra hnot
  apply he.2.2
  refine ⟨z,rfl,hl.conn ?_⟩
  intro f hf
  exact ⟨hopen f hf,fun hfe => hnot ((Set.mem_singleton_iff.mp hfe) ▸ hf)⟩

 
theorem finite_separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) :
    {e | OpenMarkedPivotal G ω {z} x e}.Finite := by
  by_cases hc : Conn G ω x z
  · obtain ⟨l,hl,_,ho⟩ := conn_exists_bond_trail G hc
    exact l.toFinset.finite_toSet.subset fun e he =>
      List.mem_toFinset.mpr (pivotal_mem_trail G ω x z l hl ho he)
  · have hempty : {e | OpenMarkedPivotal G ω {z} x e} = ∅ := by
      ext e
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨_,⟨y,hy,hxy⟩,_⟩
      exact hc ((Set.mem_singleton_iff.mp hy) ▸ hxy)
    rw [hempty]
    exact Set.finite_empty

noncomputable def separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) : Finset E :=
  (finite_separatingBonds G ω x z).toFinset

@[simp] theorem mem_separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) (e : E) :
    e ∈ separatingBonds G ω x z ↔ OpenMarkedPivotal G ω {z} x e := by
  exact (finite_separatingBonds G ω x z).mem_toFinset


end BridgeCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeGapCount
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem separatingBonds_card (G : BondGraph V E) (ω : Set E) (x z : V) :
    (separatingBonds G ω x z).card = pivotalDistance G ω x z := by
  exact Set.ncard_coe_finset (separatingBonds G ω x z) |>.symm.trans (by
    congr 1
    ext e
    exact mem_separatingBonds G ω x z e)


end BridgeGapCount

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_Replay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceContactMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def seamContactCount (G : BondGraph V E) (η : ℕ → Set E)
    (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) : ℕ :=
  (contactSet G (η i)
    (cluster G (η i ∩ internalEdges G (cluster G (ωf \ {e}) x)ᶜ) (y i))).ncard

 
noncomputable def traceContactCount (G : BondGraph V E) (η : ℕ → Set E)
    (y : ℕ → V) (ωf : Set E) (x : V) : List (ℕ × E) → ℕ → ℕ
  | [], _ => 1
  | (j,e)::c, i => if i = j then seamContactCount G η y ωf x j e
      else traceContactCount G η y ωf x c i


end TraceContactMass

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

def replaySplice (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → Set E
  | [], ω => ω
  | (i,e)::rest, ω =>
    replaySplice G x η y rest (spliceField G (cluster G ω x)
      (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i))

 
def replayMasks (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → List (ℕ × Set E)
  | [], _ => []
  | (i,e)::rest, ω =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    (i,spliceMask G S B e)::replayMasks G x η y rest (spliceField G S B e ω (η i))


end RemoteReplay

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MaskExecution
attribute [local instance] Classical.propDecidable Classical.decEq

 
def runMasks : List (ℕ × Set E) → SpliceState E → SpliceState E
  | [], s => s
  | (i,M)::ms, s => runMasks ms (exchangeState M i s)


end MaskExecution

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_ReferenceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 
abbrev FiniteField (Q : Finset E) := ↥Q.powerset

end FiniteReferenceLaw

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_MomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteTraceDistribution
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_bounded_lists {A : Type*} (Q : Finset A) (k : ℕ) :
    {c : List A | c.length ≤ k ∧ ∀ q ∈ c, q ∈ Q}.Finite := by
  have hf := (List.finite_length_le ↥Q k).image (List.map Subtype.val)
  apply hf.subset
  rintro c ⟨hc,hQ⟩
  let d : List ↥Q := c.attach.map (fun q => ⟨q.val,hQ q.val q.property⟩)
  refine ⟨d,?_,?_⟩
  · simpa only [d,List.length_map,List.length_attach,Set.mem_ofPred_eq] using hc
  · simp [d,List.map_map]

noncomputable def boundedTraceCodes (Q : Finset E) (k : ℕ) : Finset (List (ℕ × E)) :=
  (finite_bounded_lists ((Finset.Icc 1 k) ×ˢ Q) k).toFinset

@[simp] theorem mem_boundedTraceCodes (Q : Finset E) (k : ℕ) (c : List (ℕ × E)) :
    c ∈ boundedTraceCodes Q k ↔ c.length ≤ k ∧ ∀ q ∈ c, 1 ≤ q.1 ∧ q.1 ≤ k ∧ q.2 ∈ Q := by
  simp [boundedTraceCodes,Finset.mem_product,and_assoc]



noncomputable def finiteTraceCodes (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω : Set E) (Q : Finset E) : Finset (List (ℕ × E)) :=
  (boundedTraceCodes Q k).filter (fun c =>
    SpliceTrace G x η y k j ω c (replaySplice G x η y c ω))

theorem mem_finiteTraceCodes_iff (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω : Set E) (Q : Finset E) (c : List (ℕ × E)) :
    c ∈ finiteTraceCodes G x η y k j ω Q ↔ c ∈ boundedTraceCodes Q k ∧
      SpliceTrace G x η y k j ω c (replaySplice G x η y c ω) := by
  simp [finiteTraceCodes]



end FiniteTraceDistribution
end Percolation


open MeasureTheory


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev FiniteTraceIndex (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :=
  (s : ↥A) × ↥(finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q)

def traceIndexInput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : SpliceState E := a.1.val

def traceIndexCode (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : List (ℕ × E) := a.2.val

def traceIndexOutput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : SpliceState E :=
  runMasks (replayMasks G x a.1.val.2 (y a.1.val) a.2.val a.1.val.1) a.1.val



noncomputable def traceIndexMass (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : ℝ :=
  ∏ i : Fin k, (traceContactCount G a.1.val.2 (y a.1.val)
    (traceIndexOutput G x k Q A y a).1 x a.2.val (i.val+1):ℝ)⁻¹

end FiniteForwardDensity

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_TrajectoryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P : Type*}

 

abbrev FiniteChoiceTraceIndex (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V) :=
  (r : P) × FiniteTraceIndex G x k Q (A r) (y r)

def choiceTraceInput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : SpliceState E :=
  traceIndexInput G x k Q (A a.1) (y a.1) a.2

def choiceTraceOutput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : SpliceState E :=
  traceIndexOutput G x k Q (A a.1) (y a.1) a.2

noncomputable def choiceTraceMass (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) (a : FiniteChoiceTraceIndex G x k Q A y) : ℝ :=
  q (choiceTraceInput G x k Q A y a) a.1 *
    traceIndexMass G x k Q (A a.1) (y a.1) a.2

end ChoiceForwardDensity
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_EndpointKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GoodnessCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem internalEdges_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (W : Set V) :
    internalEdges G (a ⁻¹' W) = b ⁻¹' internalEdges G W := by
  ext e
  simp only [internalEdges,Set.mem_ofPred_eq,Set.mem_preimage,hab e,Sym2.mem_map]
  constructor
  · intro h y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact h z hz
  · intro h z hz
    exact h (a z) ⟨z,hz,rfl⟩

theorem cutExists_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (W : Set V) (e : E) :
    CutExists G (a ⁻¹' W) e ↔ CutExists G W (b e) := by
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨a u,a v,by rw [hab e,he,Sym2.map_mk],hu,hv⟩
  · rintro ⟨u,v,he,hu,hv⟩
    refine ⟨a.symm u,a.symm v,?_,by simpa using hu,by simpa using hv⟩
    have h := congrArg (Sym2.map a.symm) he
    simpa only [hab e,Sym2.map_map,Equiv.symm_comp_self,id_eq,Sym2.map_id',Sym2.map_mk] using h

theorem contactSet_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (W : Set V) :
    contactSet G (b ⁻¹' ω) (a ⁻¹' W) = b ⁻¹' contactSet G ω W := by
  ext e
  simp only [contactSet,Set.mem_ofPred_eq,Set.mem_preimage,cutExists_aut_preimage G hab]

end GoodnessCovariance

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_EndpointMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NoSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem SpliceExecution.nil_iff (G : BondGraph V E) (x : V) (s t : SpliceState E) :
    SpliceExecution G x s [] t ↔ s = t := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact SpliceExecution.nil s

end NoSwitchDensity

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    cluster G (b ⁻¹' ω) x = a ⁻¹' cluster G ω (a x) := by
  ext y
  exact conn_aut_iff G hab ω x y

theorem exchangeOn_preimage (b : E ≃ E) (mask ω η : Set E) :
    exchangeOn (b ⁻¹' mask) (b ⁻¹' ω) (b ⁻¹' η) = b ⁻¹' exchangeOn mask ω η := by
  rfl

theorem spliceMask_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set V) (e : E) :
    spliceMask G (a ⁻¹' S) (a ⁻¹' B) e = b ⁻¹' spliceMask G S B (b e) := by
  ext f
  simp only [spliceMask,Set.mem_insert_iff,Set.mem_ofPred_eq,Set.mem_preimage,b.injective.eq_iff]
  apply or_congr_right
  have hi : internalEdges G (a ⁻¹' S)ᶜ = b ⁻¹' internalEdges G Sᶜ :=
    internalEdges_aut_preimage G hab Sᶜ
  rw [hi]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨v,hv,hvf⟩
    refine ⟨a v,hv,?_⟩
    rw [hab f]
    exact Sym2.mem_map.mpr ⟨v,hvf,rfl⟩
  · rintro ⟨v,hv,hvf⟩
    rw [hab f] at hvf
    obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hvf
    exact ⟨w,hv,hw⟩

theorem spliceField_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set V) (e : E) (ω η : Set E) :
    spliceField G (a ⁻¹' S) (a ⁻¹' B) e (b ⁻¹' ω) (b ⁻¹' η) =
      b ⁻¹' spliceField G S B (b e) ω η := by
  rw [spliceField,spliceMask_aut_preimage G hab,exchangeOn_preimage]
  rfl

theorem seamContactCount_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) :
    seamContactCount G (fun j => b ⁻¹' η j) y (b ⁻¹' ωf) x i e =
      seamContactCount G η (fun j => a (y j)) ωf (a x) i (b e) := by
  have he : (b ⁻¹' ωf) \ {e} = b ⁻¹' (ωf \ {b e}) := by
    ext f
    simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]
  unfold seamContactCount
  rw [he,cluster_aut_preimage G hab]
  rw [show (a ⁻¹' cluster G (ωf \ {b e}) (a x))ᶜ =
    a ⁻¹' (cluster G (ωf \ {b e}) (a x))ᶜ from rfl]
  rw [internalEdges_aut_preimage G hab,← Set.preimage_inter,cluster_aut_preimage G hab,
    contactSet_aut_preimage G hab,Set.ncard_preimage_of_injective_subset_range b.injective]
  exact fun f _ => b.surjective f

end SpliceCovarianceGeometry

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

def edgeFieldEquiv (b : E ≃ E) : Set E ≃ Set E where
  toFun ω := b.symm ⁻¹' ω
  invFun ω := b ⁻¹' ω
  left_inv ω := by ext e; simp
  right_inv ω := by ext e; simp

def spliceStateEquiv (b : E ≃ E) : SpliceState E ≃ SpliceState E :=
  (edgeFieldEquiv b).prodCongr (Equiv.piCongrRight fun _ => edgeFieldEquiv b)

def spliceCodeEquiv (b : E ≃ E) : List (ℕ × E) ≃ List (ℕ × E) :=
  Equiv.listEquivOfEquiv ((Equiv.refl ℕ).prodCongr b)

@[simp] theorem edgeFieldEquiv_apply (b : E ≃ E) (ω : Set E) :
    edgeFieldEquiv b ω = b.symm ⁻¹' ω := rfl

@[simp] theorem spliceCodeEquiv_apply (b : E ≃ E) (c : List (ℕ × E)) :
    spliceCodeEquiv b c = c.map (Prod.map id b) := rfl

theorem cluster_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    cluster G (edgeFieldEquiv b ω) (a x) = a.symm ⁻¹' cluster G ω x := by
  simpa only [edgeFieldEquiv_apply,Equiv.symm_apply_apply] using
    cluster_aut_preimage G (isAut_symm G hab) ω (a x)

theorem slitCluster_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) :
    cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y) =
      a.symm ⁻¹' cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y := by
  rw [cluster_edgeFieldEquiv G hab]
  rw [show (a.symm ⁻¹' cluster G ω x)ᶜ = a.symm ⁻¹' (cluster G ω x)ᶜ from rfl]
  rw [internalEdges_aut_preimage G (isAut_symm G hab),edgeFieldEquiv_apply,← Set.preimage_inter,
    cluster_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]

theorem spliceStep_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) (e : E) :
    spliceField G (cluster G (edgeFieldEquiv b ω) (a x))
      (cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y))
      (b e) (edgeFieldEquiv b ω) (edgeFieldEquiv b η) =
    edgeFieldEquiv b (spliceField G (cluster G ω x)
      (cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) e ω η) := by
  rw [slitCluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab]
  rw [edgeFieldEquiv_apply,edgeFieldEquiv_apply,
    spliceField_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]
  rfl

 

theorem SpliceTrace.aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ)
    (ω ωf : Set E) (c : List (ℕ × E)) (ht : SpliceTrace G x η y k j ω c ωf) :
    SpliceTrace G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i)) k j
      (edgeFieldEquiv b ω) (spliceCodeEquiv b c) (edgeFieldEquiv b ωf) := by
  induction ht with
  | stop j ω hs =>
    apply SpliceTrace.stop
    simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hs
  | step j i ω e v w rest ωf hn hji hik hmax hy he hev hv hw ht ih =>
    change SpliceTrace G (a x) _ _ k j _ ((i,b e)::spliceCodeEquiv b rest) _
    refine SpliceTrace.step j i _ (b e) (a v) (a w) _ _ ?_ hji hik ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hn
    · intro l hil hlk
      rw [cluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab,
        Set.disjoint_preimage_iff a.symm.surjective]
      exact hmax l hil hlk
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hy
    · simpa only [edgeFieldEquiv_apply,Set.mem_preimage,Equiv.symm_apply_apply] using he
    · rw [hab e,hev,Sym2.map_mk]
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hv
    · simpa only [slitCluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hw
    · rw [spliceStep_edgeFieldEquiv G hab]
      exact ih

end SpliceCovarianceTrace

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceReplay
attribute [local instance] Classical.propDecidable Classical.decEq

theorem spliceStepMask_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) (e : E) :
    spliceMask G (cluster G (edgeFieldEquiv b ω) (a x))
      (cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y))
      (b e) =
    edgeFieldEquiv b (spliceMask G (cluster G ω x)
      (cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) e) := by
  rw [slitCluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab,
    spliceMask_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]
  rfl

theorem exchangeState_aut_map (b : E ≃ E) (mask : Set E) (i : ℕ) (s : SpliceState E) :
    exchangeState (edgeFieldEquiv b mask) i (spliceStateEquiv b s) =
      spliceStateEquiv b (exchangeState mask i s) := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases hji : j = i
    · subst j
      rw [exchangeState_at]
      change _ = edgeFieldEquiv b ((exchangeState mask i s).2 i)
      rw [exchangeState_at]
      rfl
    · rw [exchangeState_away _ _ _ _ hji]
      change edgeFieldEquiv b (s.2 j) = edgeFieldEquiv b ((exchangeState mask i s).2 j)
      rw [exchangeState_away _ _ _ _ hji]

theorem replaySplice_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (c : List (ℕ × E)) (ω : Set E) :
    replaySplice G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i))
      (spliceCodeEquiv b c) (edgeFieldEquiv b ω) =
    edgeFieldEquiv b (replaySplice G x η y c ω) := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    change replaySplice G (a x) _ _ (spliceCodeEquiv b c) _ = _
    rw [spliceStep_edgeFieldEquiv G hab,ih]
    rfl

theorem replayMasks_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (c : List (ℕ × E)) (ω : Set E) :
    replayMasks G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i))
      (spliceCodeEquiv b c) (edgeFieldEquiv b ω) =
    (replayMasks G x η y c ω).map (Prod.map id (edgeFieldEquiv b)) := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    simp only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,replayMasks]
    rw [spliceStepMask_edgeFieldEquiv G hab,spliceStep_edgeFieldEquiv G hab]
    exact congrArg (List.cons _) (ih _)

theorem runMasks_aut_map (b : E ≃ E) (c : List (ℕ × Set E)) (s : SpliceState E) :
    runMasks (c.map (Prod.map id (edgeFieldEquiv b))) (spliceStateEquiv b s) =
      spliceStateEquiv b (runMasks c s) := by
  induction c generalizing s with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,mask⟩
    simp only [List.map_cons,Prod.map_apply,id_eq,runMasks]
    rw [exchangeState_aut_map,ih]

theorem seamContactCount_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) :
    seamContactCount G (fun j => edgeFieldEquiv b (η j)) (fun j => a (y j))
      (edgeFieldEquiv b ωf) (a x) i (b e) = seamContactCount G η y ωf x i e := by
  simpa only [edgeFieldEquiv_apply,Equiv.symm_apply_apply] using
    seamContactCount_aut_preimage G (isAut_symm G hab) η (fun j => a (y j)) ωf (a x) i (b e)

theorem traceContactCount_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V)
    (c : List (ℕ × E)) (i : ℕ) :
    traceContactCount G (fun j => edgeFieldEquiv b (η j)) (fun j => a (y j))
      (edgeFieldEquiv b ωf) (a x) (spliceCodeEquiv b c) i =
      traceContactCount G η y ωf x c i := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨j,e⟩
    simp only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,traceContactCount]
    split_ifs
    · exact seamContactCount_aut_map G hab η y ωf x j e
    · exact ih

end SpliceCovarianceReplay

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteTraceCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem edgeFieldEquiv_symm_edgeFieldEquiv (b : E ≃ E) (ω : Set E) :
    edgeFieldEquiv b.symm (edgeFieldEquiv b ω) = ω := by
  ext e
  simp only [edgeFieldEquiv_apply,Set.mem_preimage,Equiv.symm_symm,Equiv.symm_apply_apply]

@[simp] theorem spliceStateEquiv_symm_spliceStateEquiv (b : E ≃ E) (s : SpliceState E) :
    spliceStateEquiv b.symm (spliceStateEquiv b s) = s := by
  apply Prod.ext
  · exact edgeFieldEquiv_symm_edgeFieldEquiv b s.1
  · funext i
    exact edgeFieldEquiv_symm_edgeFieldEquiv b (s.2 i)

@[simp] theorem spliceCodeEquiv_symm_spliceCodeEquiv (b : E ≃ E) (c : List (ℕ × E)) :
    spliceCodeEquiv b.symm (spliceCodeEquiv b c) = c := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    simpa only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,Equiv.symm_apply_apply] using
      congrArg (List.cons (i,e)) ih

theorem spliceTrace_aut_map_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ)
    (ω ωf : Set E) (c : List (ℕ × E)) :
    SpliceTrace G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i)) k j
      (edgeFieldEquiv b ω) (spliceCodeEquiv b c) (edgeFieldEquiv b ωf) ↔
    SpliceTrace G x η y k j ω c ωf := by
  constructor
  · intro ht
    have hh := ht.aut_map G (isAut_symm G hab) (a x) (fun i => edgeFieldEquiv b (η i))
      (fun i => a (y i)) k j (edgeFieldEquiv b ω) (edgeFieldEquiv b ωf) (spliceCodeEquiv b c)
    simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_symm_edgeFieldEquiv,
      spliceCodeEquiv_symm_spliceCodeEquiv] using hh
  · exact SpliceTrace.aut_map G hab x η y k j ω ωf c

theorem boundedTraceCodes_aut_map_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (k : ℕ) (c : List (ℕ × E)) :
    spliceCodeEquiv b c ∈ boundedTraceCodes Q' k ↔ c ∈ boundedTraceCodes Q k := by
  simp only [mem_boundedTraceCodes,spliceCodeEquiv_apply,List.length_map]
  apply and_congr_right
  intro _
  constructor
  · intro h q hq
    have hh := h (q.1,b q.2) (List.mem_map.mpr ⟨q,hq,rfl⟩)
    exact ⟨hh.1,hh.2.1,(hQ q.2).mpr hh.2.2⟩
  · intro h r hr
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact ⟨(h q hq).1,(h q hq).2.1,(hQ q.2).mp (h q hq).2.2⟩

theorem finiteTraceCodes_aut_map_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (Q Q' : Finset E) (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q')
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω : Set E) (c : List (ℕ × E)) :
    spliceCodeEquiv b c ∈ finiteTraceCodes G (a x) (fun i => edgeFieldEquiv b (η i))
      (fun i => a (y i)) k j (edgeFieldEquiv b ω) Q' ↔
      c ∈ finiteTraceCodes G x η y k j ω Q := by
  rw [mem_finiteTraceCodes_iff,mem_finiteTraceCodes_iff,boundedTraceCodes_aut_map_iff b Q Q' hQ,
    replaySplice_aut_map G hab,spliceTrace_aut_map_iff G hab]


end FiniteTraceCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteIndexCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

def finiteTraceIndexEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E) (A A' : Finset (SpliceState E))
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (hA : ∀ s, s ∈ A ↔ spliceStateEquiv b s ∈ A')
    (y y' : SpliceState E → ℕ → V) (hy : ∀ s i, y' (spliceStateEquiv b s) i = a (y s i)) :
    FiniteTraceIndex G x k Q A y ≃ FiniteTraceIndex G (a x) k Q' A' y' :=
  Equiv.sigmaCongr ((spliceStateEquiv b).subtypeEquiv hA) (fun s =>
    (spliceCodeEquiv b).subtypeEquiv (fun c => by
      have hy' : y' (spliceStateEquiv b s.val) = fun i => a (y s.val i) := funext (hy s.val)
      change c ∈ finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q ↔
        spliceCodeEquiv b c ∈ finiteTraceCodes G (a x) (fun i => edgeFieldEquiv b (s.val.2 i))
          (y' (spliceStateEquiv b s.val)) k 0 (edgeFieldEquiv b s.val.1) Q'
      rw [hy']
      exact (finiteTraceCodes_aut_map_iff G hab Q Q' hQ x s.val.2 (y s.val) k 0 s.val.1 c).symm))

namespace FiniteTraceIndexEquiv
variable (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E) (A A' : Finset (SpliceState E))
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (hA : ∀ s, s ∈ A ↔ spliceStateEquiv b s ∈ A')
    (y y' : SpliceState E → ℕ → V) (hy : ∀ s i, y' (spliceStateEquiv b s) i = a (y s i))

@[simp] theorem input (t : FiniteTraceIndex G x k Q A y) :
    traceIndexInput G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceStateEquiv b (traceIndexInput G x k Q A y t) := rfl

@[simp] theorem code (t : FiniteTraceIndex G x k Q A y) :
    traceIndexCode G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceCodeEquiv b (traceIndexCode G x k Q A y t) := rfl

@[simp] theorem output (t : FiniteTraceIndex G x k Q A y) :
    traceIndexOutput G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceStateEquiv b (traceIndexOutput G x k Q A y t) := by
  have hy' : y' (spliceStateEquiv b t.1.val) = fun i => a (y t.1.val i) := funext (hy t.1.val)
  change runMasks (replayMasks G (a x) (fun i => edgeFieldEquiv b (t.1.val.2 i))
    (y' (spliceStateEquiv b t.1.val)) (spliceCodeEquiv b t.2.val) (edgeFieldEquiv b t.1.val.1))
      (spliceStateEquiv b t.1.val) = _
  rw [hy',replayMasks_aut_map G hab,runMasks_aut_map]
  rfl

@[simp] theorem mass (t : FiniteTraceIndex G x k Q A y) :
    traceIndexMass G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      traceIndexMass G x k Q A y t := by
  unfold traceIndexMass
  rw [output G hab x k Q Q' A A' hQ hA y y' hy t]
  apply Finset.prod_congr rfl
  intro i _
  have hy' : y' (spliceStateEquiv b t.1.val) = fun i => a (y t.1.val i) := funext (hy t.1.val)
  change (traceContactCount G (fun j => edgeFieldEquiv b (t.1.val.2 j))
    (y' (spliceStateEquiv b t.1.val)) (edgeFieldEquiv b (traceIndexOutput G x k Q A y t).1)
    (a x) (spliceCodeEquiv b t.2.val) (i.val+1):ℝ)⁻¹ = _
  rw [hy',traceContactCount_aut_map G hab]

end FiniteTraceIndexEquiv



end FiniteIndexCovariance

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ChoiceIndexCovariance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P P' : Type*}

def finiteChoiceTraceIndexEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i)) :
    FiniteChoiceTraceIndex G x k Q A y ≃ FiniteChoiceTraceIndex G (a x) k Q' A' y' :=
  Equiv.sigmaCongr e (fun r => finiteTraceIndexEquiv G hab x k Q Q' (A r) (A' (e r)) hQ (hA r)
    (y r) (y' (e r)) (hy r))

namespace FiniteChoiceTraceIndexEquiv
variable (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i))

@[simp] theorem input (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceInput G (a x) k Q' A' y' (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      spliceStateEquiv b (choiceTraceInput G x k Q A y t) := rfl

@[simp] theorem output (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceOutput G (a x) k Q' A' y' (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      spliceStateEquiv b (choiceTraceOutput G x k Q A y t) :=
  FiniteTraceIndexEquiv.output G hab x k Q Q' (A t.1) (A' (e t.1)) hQ (hA t.1)
    (y t.1) (y' (e t.1)) (hy t.1) t.2

@[simp] theorem mass (q : SpliceState E → P → ℝ) (q' : SpliceState E → P' → ℝ)
    (hq : ∀ s r, q' (spliceStateEquiv b s) (e r) = q s r)
    (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceMass G (a x) k Q' A' y' q'
      (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      choiceTraceMass G x k Q A y q t := by
  unfold choiceTraceMass
  rw [input G hab x k Q Q' hQ e A A' hA y y' hy]
  change q' (spliceStateEquiv b (choiceTraceInput G x k Q A y t)) (e t.1) * _ = _
  rw [hq]
  exact congrArg (fun m => q (choiceTraceInput G x k Q A y t) t.1 * m)
    (FiniteTraceIndexEquiv.mass G hab x k Q Q' (A t.1) (A' (e t.1)) hQ (hA t.1)
      (y t.1) (y' (e t.1)) (hy t.1) t.2)

end FiniteChoiceTraceIndexEquiv

end ChoiceIndexCovariance

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_KernelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SusceptibilityTypes
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def rootSusceptibility (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (p : unitInterval) : ℝ :=
  ∑ i, weight i * susceptibility G p (root i)

end SusceptibilityTypes
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Susceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ActualSusceptibilityRightSlope
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realRootSusceptibility (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  rootSusceptibility G root weight (Set.projIcc 0 1 zero_le_one t)

@[simp] theorem realRootSusceptibility_coe (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (p : unitInterval) :
    realRootSusceptibility G root weight (p:ℝ) = rootSusceptibility G root weight p := by
  simp only [realRootSusceptibility, Set.projIcc_val]

end ActualSusceptibilityRightSlope
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_LargeContacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large Contacts for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContacts
attribute [local instance] Classical.propDecidable Classical.decEq

 
def closedContactSet (G : BondGraph V E) (A B : Set V) : Set E :=
  {e | ∃ a ∈ A, ∃ b ∈ B, G e = s(a,b)}

noncomputable def clusterContactCount (G : BondGraph V E) (ω : Set E) (x v : V) : ℕ :=
  (closedContactSet G (cluster G ω x) (cluster G ω v)).ncard

end InfiniteContacts
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullLargeContacts
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def fullLargeContact (G : BondGraph V E) (x v : V) (L : ℕ) (ω : Set E) : ℝ :=
  if ¬Conn G ω x v ∧ L ≤ min (cluster G ω x).ncard (cluster G ω v).ncard
  then clusterContactCount G ω x v else 0

end FullLargeContacts
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_RussoRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Russo Rows for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section PointwiseRussoLimit
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realContactExpectation (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  ∫ ω, fullLargeContact G x y 0 ω ∂law (Set.projIcc 0 1 zero_le_one t)

@[simp] theorem realContactExpectation_coe (G : BondGraph V E) (x y : V) (p : unitInterval) :
    realContactExpectation G x y (p:ℝ) = ∫ ω, fullLargeContact G x y 0 ω ∂law p := by
  simp only [realContactExpectation,Set.projIcc_val]

noncomputable def realTwoPoint (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  twoPoint G (Set.projIcc 0 1 zero_le_one t) x y

@[simp] theorem realTwoPoint_coe (G : BondGraph V E) (x y : V) (p : unitInterval) :
    realTwoPoint G x y (p:ℝ) = twoPoint G p x y := by
  simp only [realTwoPoint,Set.projIcc_val]

end PointwiseRussoLimit
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
theorem isAut_refl (G : BondGraph V E) : IsAut G (Equiv.refl V) (Equiv.refl E) := by
  intro e
  simp

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Subdivision_Graph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision of indexed bond graphs and its basic geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory

abbrev SubdivisionEdge (G : BondGraph V E) := {ev : E × V // ev.2 ∈ G ev.1}

def subdivision (G : BondGraph V E) : BondGraph (V ⊕ E) (SubdivisionEdge G) :=
  fun ev => s(Sum.inl ev.val.2, Sum.inr ev.val.1)

@[simp] theorem subdivision_adj_inl_inr (G : BondGraph V E) (x : V) (e : E) :
    Adj (subdivision G) (.inl x) (.inr e) ↔ x ∈ G e := by
  constructor
  · rintro ⟨⟨⟨f,y⟩,hy⟩,h⟩
    simp only [subdivision,Sym2.eq_iff] at h
    rcases h with ⟨hyx,hfe⟩ | ⟨hbad,_⟩
    · have : y = x := Sum.inl.inj hyx
      have : f = e := Sum.inr.inj hfe
      subst y; subst f; exact hy
    · cases hbad
  · intro hx
    exact ⟨⟨(e,x),hx⟩,rfl⟩

@[simp] theorem subdivision_adj_inl_inl (G : BondGraph V E) (x y : V) :
    ¬ Adj (subdivision G) (.inl x) (.inl y) := by
  rintro ⟨⟨⟨e,z⟩,hz⟩,h⟩
  simp [subdivision] at h

@[simp] theorem subdivision_adj_inr_inr (G : BondGraph V E) (e f : E) :
    ¬ Adj (subdivision G) (.inr e) (.inr f) := by
  rintro ⟨⟨⟨d,z⟩,hz⟩,h⟩
  simp [subdivision] at h

@[simp] theorem subdivision_adj_inr_inl (G : BondGraph V E) (e : E) (x : V) :
    Adj (subdivision G) (.inr e) (.inl x) ↔ x ∈ G e := by
  exact ⟨fun h => (subdivision_adj_inl_inr G x e).mp (adj_symm _ h),
    fun h => adj_symm _ ((subdivision_adj_inl_inr G x e).mpr h)⟩

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Subdivision_Coupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coupling percolation on a graph with percolation on its subdivision. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def halfBit (G : BondGraph V E) : SubdivisionEdge G ↪ E × Bool := by
  classical
  refine ⟨fun ev => (ev.val.1,if ev.val.2 = (G ev.val.1).out.1 then false else true),?_⟩
  rintro ⟨⟨e,x⟩,hx⟩ ⟨⟨f,y⟩,hy⟩ h
  have hef : e = f := congrArg Prod.fst h
  subst f
  have hb := congrArg Prod.snd h
  dsimp only at hb
  have he : G e = s((G e).out.1,(G e).out.2) := (G e).out_eq.symm
  have hx' : x = (G e).out.1 ∨ x = (G e).out.2 := by
    apply Sym2.mem_iff.mp
    rw [←he]
    exact hx
  have hy' : y = (G e).out.1 ∨ y = (G e).out.2 := by
    apply Sym2.mem_iff.mp
    rw [←he]
    exact hy
  have hxy : x = y := by
    by_cases h₁ : x = (G e).out.1 <;> by_cases h₂ : y = (G e).out.1
    · exact h₁.trans h₂.symm
    · simp only [ite_eq_left h₁,ite_eq_right h₂,Bool.false_eq_true] at hb
    · simp only [ite_eq_right h₁,ite_eq_left h₂,Bool.true_eq_false] at hb
    · exact (hx'.resolve_left h₁).trans (hy'.resolve_left h₂).symm
  subst y
  rfl

@[simp] theorem halfBit_fst (G : BondGraph V E) (e : SubdivisionEdge G) :
    (halfBit G e).1 = e.val.1 := rfl


end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation

/-- An undirected graph with labelled bonds, including loops and parallel bonds. -/
structure BondGraph (V E : Type*) where
  ends : E → Sym2 V

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

/-- The graph of retained bonds. `fromEdgeSet` discards loops. -/
def openGraph (ω : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' ω)

/-- The underlying connectivity graph with every bond retained. -/
def fullGraph : SimpleGraph V := G.openGraph Set.univ

/-- Local finiteness counts bonds, not just distinct neighbors. -/
def LocallyFinite : Prop := ∀ v : V, {e : E | v ∈ G.ends e}.Finite

/-- Automorphisms preserve the vertex and bond structure, including multiplicities. -/
structure Aut where
  vertex : V ≃ V
  edge : E ≃ E
  preserves : ∀ e, G.ends (edge e) = Sym2.map vertex (G.ends e)

/-- Finitely many vertex orbits under the full automorphism group. -/
def QuasiTransitive : Prop :=
  ∃ S : Set V, S.Finite ∧ ∀ v : V, ∃ s ∈ S, ∃ φ : G.Aut, φ.vertex s = v

/-- Finite open paths, including the path of length zero, define the open cluster. -/
def cluster (ω : Set E) (v : V) : Set V := {w | (G.openGraph ω).Reachable v w}

/-- The event that at least one open cluster is infinite. -/
def percolates : Set (Set E) := {ω | ∃ v : V, (G.cluster ω v).Infinite}

/-- Independent retention with parameter `p ∈ [0,1]` of each labelled bond. -/
noncomputable def law (_G : BondGraph V E) (p : unitInterval) : Measure (Set E) :=
  ProbabilityTheory.setBernoulli Set.univ p

/-- The infimum of parameters with positive probability of an infinite cluster. -/
noncomputable def criticalProbability : unitInterval :=
  sInf {p : unitInterval | 0 < G.law p G.percolates}

end BondGraph
end CriticalPercolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem finite_neighbors (hlocal : G.LocallyFinite) (v : V) :
    (G.fullGraph.neighborSet v).Finite := by
  classical
  have hf : (⋃ e ∈ {e : E | v ∈ G.ends e}, (↑(G.ends e).toFinset : Set V)).Finite :=
    (hlocal v).biUnion fun e _ => (G.ends e).toFinset.finite_toSet
  apply hf.subset
  intro w hw
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hw
  apply Set.mem_iUnion₂.mpr
  refine ⟨e, ?_, ?_⟩ <;> simp [he]

def vertexBall (G : BondGraph V E) (o : V) : ℕ → Set V
  | 0 => {o}
  | n + 1 => G.vertexBall o n ∪ ⋃ v ∈ G.vertexBall o n, G.fullGraph.neighborSet v

lemma vertexBall_finite (hlocal : G.LocallyFinite) (o : V) (n : ℕ) :
    (G.vertexBall o n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton o
  | succ n ih => exact ih.union (ih.biUnion fun v _ => G.finite_neighbors hlocal v)

lemma reachable_mem_vertexBall {o v : V} (h : G.fullGraph.Reachable o v) :
    ∃ n, v ∈ G.vertexBall o n := by
  have hr := (G.fullGraph.reachable_iff_reflTransGen o v).mp h
  clear h
  induction hr with
  | refl => exact ⟨0, rfl⟩
  | @tail u w hr huv ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr (Set.mem_iUnion₂.mpr ⟨u, hn, huv⟩)⟩

def lengthReach (H : SimpleGraph V) : ℕ → V → V → Prop
  | 0, v, w => v = w
  | n + 1, v, w => ∃ u, lengthReach H n v u ∧ H.Adj u w

lemma reachable_iff_exists_lengthReach (H : SimpleGraph V) (v w : V) :
    H.Reachable v w ↔ ∃ n, lengthReach H n v w := by
  rw [H.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail u w h huw ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, u, hn, huw⟩
  · rintro ⟨n, hn⟩
    induction n generalizing w with
    | zero => exact hn ▸ Relation.ReflTransGen.refl
    | succ n ih =>
        obtain ⟨u, hu, huw⟩ := hn
        exact (ih u hu).tail huw

lemma measurable_openGraph_adj [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.openGraph ω).Adj v w) := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  exact (Measurable.exists fun e =>
    (measurable_set_mem e).and measurable_const).and measurable_const

lemma measurable_lengthReach [Countable V] [Countable E] (n : ℕ) (v w : V) :
    Measurable (fun ω : Set E => lengthReach (G.openGraph ω) n v w) := by
  induction n generalizing w with
  | zero => exact measurable_const
  | succ n ih =>
      exact Measurable.exists fun u => (ih u).and (G.measurable_openGraph_adj u w)

lemma measurable_reachable [Countable V] [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.openGraph ω).Reachable v w) := by
  simp_rw [reachable_iff_exists_lengthReach]
  exact Measurable.exists fun n => G.measurable_lengthReach n v w

@[simp] lemma openGraph_empty : G.openGraph ∅ = ⊥ := by
  simp [openGraph]

@[simp] lemma cluster_empty (v : V) : G.cluster ∅ v = {v} := by
  ext w
  simp [cluster, SimpleGraph.reachable_bot, eq_comm]

@[simp] lemma empty_not_percolates : ∅ ∉ G.percolates := by
  simp [percolates]

end BondGraph

namespace ClusterDeletion
variable {V : Type*}

def delete (H : SimpleGraph V) (U : Set V) : SimpleGraph V where
  Adj v w := H.Adj v w ∧ v ∉ U ∧ w ∉ U
  symm.symm _v _w h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl v h := H.loopless.irrefl v h.1

def roots (H : SimpleGraph V) (S : Set V) : Set V :=
  {v | ∃ s ∈ S, H.Reachable s v}

def component (H : SimpleGraph V) (s : V) : Set V :=
  {v | H.Reachable s v}

lemma roots_self (H : SimpleGraph V) (S : Set V) : S ⊆ roots H S :=
  fun s hs => ⟨s, hs, .refl _⟩

lemma roots_closed {H : SimpleGraph V} {S : Set V} {v w : V}
    (hv : v ∈ roots H S) (hvw : H.Adj v w) : w ∈ roots H S := by
  obtain ⟨s, hs, hsv⟩ := hv
  exact ⟨s, hs, hsv.trans hvw.reachable⟩

lemma reachable_mem_of_closed {H : SimpleGraph V} {U : Set V}
    (hU : ∀ ⦃v w⦄, v ∈ U → H.Adj v w → w ∈ U) {s v : V}
    (hs : s ∈ U) (hsv : H.Reachable s v) : v ∈ U := by
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact hs
  | tail _ huv ih => exact hU ih huv

lemma roots_subset_of_adj {H H' : SimpleGraph V} (S : Set V)
    (hh : ∀ ⦃v w⦄, v ∈ roots H S → H.Adj v w → H'.Adj v w) :
    roots H S ⊆ roots H' S := by
  rintro v ⟨s, hs, hsv⟩
  refine ⟨s, hs, ?_⟩
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact .refl _
  | @tail u v hr huv ih =>
      exact ih.trans (hh ⟨s, hs, (H.reachable_iff_reflTransGen s u).mpr hr⟩ huv).reachable

lemma roots_eq_of_adj_eq_incident {H H' : SimpleGraph V} {S U : Set V}
    (hU : roots H S = U)
    (hh : ∀ ⦃v w⦄, v ∈ U → (H.Adj v w ↔ H'.Adj v w)) :
    roots H' S = U := by
  subst U
  apply Set.Subset.antisymm
  · rintro v ⟨s, hs, hsv⟩
    exact reachable_mem_of_closed
      (fun {_ _} hv hvw => roots_closed hv ((hh hv).mpr hvw)) (roots_self H S hs) hsv
  · exact roots_subset_of_adj S fun {_ _} hv hvw => (hh hv).mp hvw

end ClusterDeletion
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def incidentEdges (U : Set V) : Set E := {e | ∃ v ∈ U, v ∈ G.ends e}

lemma openGraph_adj_eq_of_incident {U : Set V} {ω ω' : Set E}
    (hω : ∀ e ∈ G.incidentEdges U, e ∈ ω ↔ e ∈ ω') {v w : V} (hv : v ∈ U) :
    (G.openGraph ω).Adj v w ↔ (G.openGraph ω').Adj v w := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ G.incidentEdges U := by
    intro e heq
    exact ⟨v, hv, by simp [heq]⟩
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mpr heω, heq⟩, hne⟩

lemma roots_eq_of_incident {S U : Set V} {ω ω' : Set E}
    (hU : ClusterDeletion.roots (G.openGraph ω) S = U)
    (hω : ∀ e ∈ G.incidentEdges U, e ∈ ω ↔ e ∈ ω') :
    ClusterDeletion.roots (G.openGraph ω') S = U :=
  ClusterDeletion.roots_eq_of_adj_eq_incident hU (fun {_ _} hv => G.openGraph_adj_eq_of_incident hω hv)

end BondGraph
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OpenGraphIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

instance law_probability (p : unitInterval) : IsProbabilityMeasure (G.law p) := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma Aut.adj_map (φ : G.Aut) (ω : Set E) (v w : V) :
    (G.openGraph (φ.edge '' ω)).Adj (φ.vertex v) (φ.vertex w) ↔
      (G.openGraph ω).Adj v w := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  constructor
  · rintro ⟨⟨e, ⟨f, hf, rfl⟩, hend⟩, hne⟩
    rw [φ.preserves, ← Sym2.map_mk] at hend
    exact ⟨⟨f, hf, Sym2.map.injective φ.vertex.injective hend⟩,
      fun h => hne (congrArg φ.vertex h)⟩
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨φ.edge e, ⟨e, he, rfl⟩, ?_⟩, ?_⟩
    · rw [φ.preserves, hend, Sym2.map_mk]
    · exact fun h => hne (φ.vertex.injective h)

noncomputable def Aut.openGraphIso (φ : G.Aut) (ω : Set E) :
    G.openGraph ω ≃g G.openGraph (φ.edge '' ω) where
  toEquiv := φ.vertex
  map_rel_iff' := fun {v w} => Aut.adj_map G φ ω v w

def infiniteEvent (o : V) : Set (Set E) := {ω | (G.cluster ω o).Infinite}

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexBall_mono (o : V) : Monotone (G.vertexBall o) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

lemma mem_vertexBall_self (o : V) (n : ℕ) : o ∈ G.vertexBall o n :=
  G.vertexBall_mono o (Nat.zero_le n) rfl

lemma vertexBall_step {o v w : V} {n : ℕ} (hv : v ∈ G.vertexBall o n)
    (he : G.fullGraph.Adj v w) : w ∈ G.vertexBall o (n+1) :=
  Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,he⟩)

lemma vertexBall_add {o v : V} {n : ℕ} (hv : v ∈ G.vertexBall o n) (m : ℕ) :
    G.vertexBall v m ⊆ G.vertexBall o (n+m) := by
  induction m with
  | zero => simpa only [vertexBall,Nat.add_zero,Set.singleton_subset_iff] using hv
  | succ m ih =>
    rintro w (hw | hw)
    · exact G.vertexBall_mono o (by omega) (ih hw)
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hw
      exact G.vertexBall_step (ih hz) hzw

lemma vertexBall_comm {o v : V} {n : ℕ} : v ∈ G.vertexBall o n ↔ o ∈ G.vertexBall v n := by
  have h : ∀ n (o v : V), v ∈ G.vertexBall o n → o ∈ G.vertexBall v n := by
    intro n
    induction n with
    | zero => intro o v hv; simpa only [vertexBall,Set.mem_singleton_iff] using hv.symm
    | succ n ih =>
      intro o v hv
      rcases hv with hv | hv
      · exact G.vertexBall_mono v (Nat.le_succ n) (ih o v hv)
      · obtain ⟨z,hz,hzv⟩ := Set.mem_iUnion₂.mp hv
        have h1 : z ∈ G.vertexBall v 1 := G.vertexBall_step (G.mem_vertexBall_self v 0) hzv.symm
        simpa only [Nat.add_comm 1] using G.vertexBall_add h1 n (ih o z hz)
  exact ⟨h n o v,h n v o⟩

lemma Aut.fullGraph_adj (φ : G.Aut) (u v : V) :
    G.fullGraph.Adj (φ.vertex u) (φ.vertex v) ↔ G.fullGraph.Adj u v := by
  simpa only [fullGraph,Set.image_univ,Equiv.range_eq_univ] using Aut.adj_map G φ Set.univ u v

lemma Aut.vertexBall_mem (φ : G.Aut) (o v : V) (n : ℕ) :
    φ.vertex v ∈ G.vertexBall (φ.vertex o) n ↔ v ∈ G.vertexBall o n := by
  induction n generalizing v with
  | zero => simp only [vertexBall,Set.mem_singleton_iff,φ.vertex.injective.eq_iff]
  | succ n ih =>
    simp only [vertexBall,Set.mem_union,Set.mem_iUnion,exists_prop,SimpleGraph.mem_neighborSet]
    constructor
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mp h)
      · obtain ⟨w,rfl⟩ := φ.vertex.surjective z
        exact Or.inr ⟨w,(ih w).mp hz,
          (Aut.fullGraph_adj G φ w v).mp hzv⟩
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mpr h)
      · exact Or.inr ⟨φ.vertex z,(ih z).mpr hz,(Aut.fullGraph_adj G φ z v).mpr hzv⟩

lemma finite_subset_vertexBall (hconnected : G.fullGraph.Connected)
    (o : V) {S : Set V} (hS : S.Finite) : ∃ n, S ⊆ G.vertexBall o n := by
  have hh : ∀ v : S, ∃ n, v.val ∈ G.vertexBall o n :=
    fun v => G.reachable_mem_vertexBall (hconnected o v)
  choose n hn using hh
  let := hS.fintype
  refine ⟨∑ v : S, n v,?_⟩
  intro v hv
  exact G.vertexBall_mono o (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨v,hv⟩ : S))) (hn ⟨v,hv⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SubexponentialVolumes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def SubexponentialGrowth : Prop :=
  ∀ o : V, ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n≥N,
    Real.log ((G.vertexBall o n).ncard : ℝ) ≤ ε*n

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_Earlier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V : Type*} {n : ℕ}

def earlier (x : Fin n → V) (k : Fin n) : Set V := {v | ∃ j < k, x j = v}
def first (H : SimpleGraph V) (x : Fin n → V) (k : Fin n) : Prop :=
  x k ∉ roots H (earlier x k)
noncomputable def select (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) : ℝ :=
  if first H x k ∧ x i ∈ component H (x k) then 1 else 0

end CriticalPercolation.ClusterColumns

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ExpectedCluster
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def expectedCluster (w : E → Prop → ℝ) (s : V)
    (F : Set V → ℝ) (W : Set V) : ℝ :=
  expect w (fun ω => F (component (delete (G.openGraph ω) W) s))

noncomputable def expectedResidual (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact expect w (fun ω =>
    if s ∉ roots (delete (G.openGraph ω) U) S then
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S ∪ U)
    else 0)

end CriticalPercolation.BondGraph

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterUpdate
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

open scoped Classical

noncomputable def clusterUpdate (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ :=
  expect w (fun ω => G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S))

noncomputable def avoidedAverage (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) : ℝ := by
  classical
  exact expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
    F (component (G.openGraph ω) s) else 0)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_HitOthers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open scoped Classical

variable {V : Type*} {n : ℕ}

noncomputable def hitOthers (x : Fin n → V) (k : Fin n) (U : Set V) : ℝ :=
  if ∃ j, j ≠ k ∧ x j ∈ U then 1 else 0

end CriticalPercolation.ClusterColumns

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_Column
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def column {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) (i : Fin n) : ℝ :=
  expect w (fun ω => select (G.openGraph ω) x k i * F (component (G.openGraph ω) (x k)))

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_UpdateKernel
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def updateKernel (w : E → Prop → ℝ) (S : Set V) (s : V)
    (U Z : Set V) : ℝ :=
  G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0) U

noncomputable def avoidedLaw (w : E → Prop → ℝ) (S : Set V) (s : V) (U : Set V) : ℝ :=
  G.avoidedAverage w S s (fun Z => if Z = U then 1 else 0) /
    G.avoidedAverage w S s (fun _ => 1)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_ClusterMatrix
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def clusterMatrix {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    Matrix (Fin n) (Fin n) ℝ := fun i k => G.column w x k (fun _ => 1) i

noncomputable def inverseColumn {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) : Fin n → ℝ :=
  (G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k F

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_RestrictVertices
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

noncomputable def restrictVertices (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) : BondGraph U E where
  ends e := (G.ends e).attachWith (hU e)

open CriticalPercolation.ClusterColumns CriticalPercolation.ClusterDeletion
open CriticalPercolation.FiniteProduct

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def hitEvent (o : V) (A : Set V) : Set (Set E) :=
  {ω | (G.cluster ω o ∩ A).Nonempty}

lemma measurableSet_hitEvent [Countable V] [Countable E] (o : V) (A : Set V) :
    MeasurableSet (G.hitEvent o A) := by
  exact (Measurable.exists fun v => (G.measurable_reachable o v).and measurable_const).setOf

def restrictEdges (s : Set E) : BondGraph V s where
  ends e := G.ends e

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteOpenWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def HasFiniteOpenWitness (A : Set (Set E)) : Prop :=
  ∀ ω ∈ A, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ s ∈ A

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterTail (o : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster ω o ∧ n ≤ K.ncard}

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryInterpolation
open scoped Classical

def midpoint (l r : ℕ) : ℕ := (l+r)/2

def bisect (l r : ℕ) (side : Bool) : ℕ × ℕ :=
  if r ≤ l+1 then (l,r) else if side then (midpoint l r,r) else (l,midpoint l r)

def terminal (l r : ℕ) : List Bool → ℕ × ℕ
  | [] => (l,r)
  | b::bs => terminal (bisect l r b).1 (bisect l r b).2 bs

end CriticalPercolation.BinaryInterpolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SearchTree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation

inductive SearchTree (E R : Type*) where
  | done (r : R)
  | ask (e : E) (left right : SearchTree E R)

namespace LazyDFS
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

abbrev Dart (V E : Type*) := V × E × V

structure State (V E : Type*) where
  reached : Finset V
  read : Finset E

def State.closed (s : State V E) (e : E) : State V E := ⟨s.reached,insert e s.read⟩
def State.opened (s : State V E) (e : E) (v : V) : State V E :=
  ⟨insert v s.reached,insert e s.read⟩

def push (G : BondGraph V E) (order : List (Dart V E)) (v : V) : List (Dart V E) :=
  order.filter fun d => d.1 = v ∧ G.ends d.2.1 = s(d.1,d.2.2)

noncomputable def compile (G : BondGraph V E) (order : List (Dart V E)) (B : Set V) :
    ℕ → State V E → List (Dart V E) → SearchTree E (State V E)
  | 0, st, _ => .done st
  | n+1, st, stack =>
    if ∃ v ∈ st.reached, v ∈ B then .done st else
    match stack with
    | [] => .done st
    | d :: rest =>
      if d.2.2 ∈ st.reached ∨ d.2.1 ∈ st.read ∨ d.1 ∉ st.reached ∨
        G.ends d.2.1 ≠ s(d.1,d.2.2) then compile G order B n st rest else
      .ask d.2.1 (compile G order B n (st.closed d.2.1) rest)
        (compile G order B n (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest))

variable [Fintype V]

def rank (order : List (Dart V E)) (st : State V E) (stack : List (Dart V E)) : ℕ :=
  (Fintype.card V - st.reached.card)*(order.length+1)+stack.length

end LazyDFS
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Initial
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

noncomputable def initial (w : V) : State V E := ⟨{w},∅⟩

variable [Fintype V]

noncomputable def search (G : BondGraph V E) (order : List (Dart V E)) (w : V) (B : Set V) :
    SearchTree E (State V E) :=
  compile G order B (rank order (initial w) (push G order w)) (initial w) (push G order w)

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterObject
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

abbrev ClusterObject (V E : Type*) := Set V × Set E

def clusterObject (ω : Set E) (S : Set V) : ClusterObject V E :=
  (roots (G.openGraph ω) S, ω ∩ G.incidentEdges (roots (G.openGraph ω) S))

def eraseVertices (ω : Set E) (U : Set V) : Set E := ω \ G.incidentEdges U

lemma clusterObject_eq_of_incident {S : Set V} {C : ClusterObject V E} {ω ω' : Set E}
    (hC : G.clusterObject ω S = C)
    (hω : ∀ e ∈ G.incidentEdges C.1, e ∈ ω ↔ e ∈ ω') :
    G.clusterObject ω' S = C := by
  have hr : roots (G.openGraph ω) S = C.1 := congrArg Prod.fst hC
  have hr' := G.roots_eq_of_incident hr hω
  apply Prod.ext hr'
  change ω' ∩ G.incidentEdges (roots (G.openGraph ω') S) = C.2
  have he : ω ∩ G.incidentEdges (roots (G.openGraph ω) S) = C.2 := congrArg Prod.snd hC
  rw [hr] at he
  rw [hr', ← he]
  ext e
  constructor
  · intro hh
    exact ⟨(hω e hh.2).mpr hh.1, hh.2⟩
  · intro hh
    exact ⟨(hω e hh.2).mp hh.1, hh.2⟩

lemma dependsOn_exact_clusterObject (S : Set V) (C : ClusterObject V E) :
    DependsOn (fun ω : Set E => G.clusterObject ω S = C) (G.incidentEdges C.1) := by
  intro ω ω' hω
  apply propext
  constructor
  · exact fun h => G.clusterObject_eq_of_incident h (fun e he => (hω e he).to_iff)
  · exact fun h => G.clusterObject_eq_of_incident h (fun e he => (hω e he).symm.to_iff)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_ObjectKernel
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def objectKernel (w : E → Prop → ℝ) (S : Set V)
    (C D : ClusterObject V E) : ℝ :=
  distribution w (fun ω => G.clusterObject (G.eraseVertices ω C.1) S) D

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ObjectAvoidMass
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def objectAvoidMass (w : E → Prop → ℝ) (A B : Set V)
    (C : ClusterObject V E) : ℝ :=
  if Disjoint C.1 B then distribution w (fun ω => G.clusterObject ω A) C else 0

noncomputable def objectAvoidTotal (w : E → Prop → ℝ) (A B : Set V) : ℝ :=
  expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then 1 else 0)

noncomputable def objectAvoidLaw (w : E → Prop → ℝ) (A B : Set V)
    (C : ClusterObject V E) : ℝ := G.objectAvoidMass w A B C/G.objectAvoidTotal w A B

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_IsolateThree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

def isolateThree (a s t : V) (ω : Set E) : Prop :=
  ¬(G.openGraph ω).Reachable a s ∧ ¬(G.openGraph ω).Reachable a t

def separateThree (a s t : V) (ω : Set E) : Prop :=
  G.isolateThree a s t ω ∧ ¬(G.openGraph ω).Reachable s t

def joinedPair (a s t : V) (ω : Set E) : Prop :=
  G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable s t

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_WiredEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

def wiredEvent (a s t : V) (ω : Set E) : Prop :=
  ((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EraseBond
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

noncomputable def eraseBond (f : E) (o : V) : BondGraph V E :=
  ⟨Function.update G.ends f s(o,o)⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_Connects
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

def connects (a t : V) (ω : Set E) : Prop := (G.openGraph ω).Reachable a t

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_MapVertices
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E U : Type*} (G : BondGraph V E)

def mapVertices (f : V → U) : BondGraph U E := ⟨Sym2.map f ∘ G.ends⟩

open scoped Classical

noncomputable def collapseTarget (B : Set V) (v : V) : Option V :=
  if v ∈ B then none else some v
noncomputable def wireTargets (B : Set V) : BondGraph (Option V) E :=
  G.mapVertices (collapseTarget B)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def contactScore (T : SearchTree E R) (p : ℝ) (C : Set E)
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : E → Prop) : ℝ :=
  match T with
  | .done _ => 0
  | .ask e l r => (if e ∈ C then p*delta w F e else 0) +
      if ω e then r.contactScore p C F (pin w e True) ω
      else l.contactScore p C F (pin w e False) ω

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CutEdges
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical

variable {V E : Type*}

def cutEdges (G : BondGraph V E) (O : Set V) : Set E :=
  {e | ∃ x y, G.ends e = s(x,y) ∧ x ∉ O ∧ y ∈ O}

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryDelta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def queryDelta (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r => if e = f then delta w F f else
      if ω f then r.queryDelta F (pin w f True) ω e
      else l.queryDelta F (pin w f False) ω e

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SequentialExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

structure Exposure (E A B : Type*) where
  record : (E → A) → B
  domain : B → Set E
  bits : B → E → A
  atom : ∀ b, DependsOn (fun ω => record ω = b) (domain b)
  exact : ∀ ω e, e ∈ domain (record ω) → bits (record ω) e = ω e

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def incidenceExposure (G : BondGraph V E) (S : Set V) :
    Exposure E Prop (ClusterObject V E) where
  record := fun ω => G.clusterObject ω S
  domain := fun C => G.incidentEdges C.1
  bits := Prod.snd
  atom := G.dependsOn_exact_clusterObject S
  exact := by
    intro ω e he
    apply propext
    change ω e ∧ e ∈ G.incidentEdges (G.clusterObject ω S).1 ↔ ω e
    exact ⟨fun h => h.1,fun h => ⟨h,he⟩⟩

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def scheduledContact (order : List (LazyDFS.Dart V E))
    (B : Set V) (a : V) (p : ℝ) (w : E → Prop → ℝ)
    (C : ClusterObject V E) (ω : E → Prop) : ℝ :=
  if a ∈ C.1 then 1 else
    (LazyDFS.search G order a B).contactScore p (G.cutEdges C.1)
      (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*}

def anchorSet (S : Set V) (a : ℕ → V) (n : ℕ) : Set V :=
  S ∪ a '' {i | i<n}

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

noncomputable def contactWeight (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (e : E) : ℝ :=
  if e ∈ G.cutEdges O then p*(LazyDFS.search G order a B).queryDelta
    (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω e else 0

noncomputable def contactKernel (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) : ℝ :=
  if a ∈ C.1 then if mark = none then 1 else 0 else
    match mark with
    | none => 0
    | some e => G.contactWeight order B C.1 a p w ω e /
        prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryLaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

universe uE

def History (E : Type uE) : ℕ → Type uE
  | 0 => PUnit
  | n+1 => History E n × Bool × Option E

instance historyFintype {E : Type*} [Fintype E] : (n : ℕ) → Fintype (History E n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
    letI := historyFintype (E := E) n
    exact inferInstanceAs (Fintype (History E n × Bool × Option E))

def interval {E : Type*} (d : ℕ) : (n : ℕ) → History E n → ℕ × ℕ
  | 0, _ => (0,d)
  | n+1, h => bisect (interval d n h.1).1 (interval d n h.1).2 h.2.1

def nextIndex {E : Type*} (d : ℕ) (n : ℕ) (h : History E n) : ℕ :=
  if (interval d n h).2 ≤ (interval d n h).1+1 then (interval d n h).1
    else midpoint (interval d n h).1 (interval d n h).2

def anchors {V E : Type*} (d : ℕ) (x : ℕ → V) : (n : ℕ) → History E n → List (V × Bool)
  | 0, _ => [(x 0,true),(x d,false)]
  | n+1, h => anchors d x n h.1 ++ [(x (nextIndex d n h.1),h.2.1)]

def anchorSet {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) : Set V :=
  {v | ∃ b, (v,b) ∈ anchors d x n h}

noncomputable def firstIndex (P : ℕ → Prop) : ℕ :=
  if h : ∃ j, P j then Nat.find h else 0

variable {V E : Type*} (G : BondGraph V E)

def parentPredicate (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) (j : ℕ) : Prop :=
  ∃ z, L[j]? = some z ∧ match m with
    | none => (G.openGraph ω).Reachable a z.1
    | some e => ∃ v ∈ G.ends e, (G.openGraph ω).Reachable z.1 v

noncomputable def parent (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) : ℕ :=
  firstIndex (parentPredicate G L a ω m)

noncomputable def side (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) : Bool :=
  ((L[parent G L a ω m]?).getD (a,true)).2

section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

noncomputable def density : (n : ℕ) → History E n → (E → Prop) → ℝ
  | 0, _, ω => r₀ ω
  | n+1, h, ω =>
    if side G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 = h.2.1 then
      density n h.1 ω * G.contactKernel order (anchorSet d x n h.1)
        (x (nextIndex d n h.1)) p w (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2
      else 0

end Density

section Seed
variable [Fintype V] [Fintype E]

def endpointEvent (u v : V) (s : ℕ) (ω : Set E) : Prop :=
  ¬ (G.openGraph ω).Reachable u v ∧
    s ≤ (G.cluster ω u).toFinset.card ∧ s ≤ (G.cluster ω v).toFinset.card

noncomputable def seed (w : E → Prop → ℝ) (u v : V) (s : ℕ) (ω : E → Prop) : ℝ :=
  (prob w (endpointEvent G u v s))⁻¹ * if endpointEvent G u v s ω then 1 else 0

end Seed

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinarySupport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*} (G : BondGraph V E)

def Consistent (L : List (V × Bool)) (ω : Set E) : Prop :=
  ∀ z ∈ L, ∀ t ∈ L, (G.openGraph ω).Reachable z.1 t.1 → z.2=t.2

def sideWord {E : Type*} : (n : ℕ) → History E n → List Bool
  | 0, _ => []
  | n+1, h => sideWord n h.1 ++ [h.2.1]

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_AncestryForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest

structure Forest where
  parent : ℕ → ℕ
  parent_lt : ∀ n, 2 ≤ n → parent n < n

namespace Forest
variable (F : Forest)

def lineage (F : Forest) (n : ℕ) : List ℕ :=
  if _h : n < 2 then [n] else n :: F.lineage (F.parent n)
termination_by n
decreasing_by exact F.parent_lt n (by omega)

end Forest
end CriticalPercolation.InterpolationForest

namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

def active (u v : ℕ) : Finset ℕ :=
  ((F.lineage u ++ F.lineage v).toFinset).filter (fun i => 2 ≤ i)

end CriticalPercolation.InterpolationForest.Forest
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryForest
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

noncomputable def nodeParent (d : ℕ) (x : ℕ → V) (ω : Set E) :
    (n : ℕ) → History E n → ℕ → ℕ
  | 0, _, i => if i=1 then 1 else 0
  | n+1, h, i => if i=n+2 then
      let j := parent G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2
      if j<n+2 then j else 0
    else nodeParent d x ω n h.1 i

lemma nodeParent_lt (d : ℕ) (x : ℕ → V) (ω : Set E) (n : ℕ) (h : History E n)
    (i : ℕ) (hi : 2 ≤ i) : nodeParent G d x ω n h i < i := by
  induction n with
  | zero => simp only [nodeParent,ite_eq_right (by omega : i≠1)]; omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      simp only [nodeParent,if_true]
      split_ifs with hp
      · exact hp
      · omega
    · rw [nodeParent,ite_eq_right he]
      exact ih h.1

noncomputable def historyForest (d : ℕ) (x : ℕ → V) (ω : Set E)
    (n : ℕ) (h : History E n) : Forest :=
  ⟨nodeParent G d x ω n h, nodeParent_lt G d x ω n h⟩

def node (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) : V × Bool :=
  (anchors d x n h)[i]?.getD (x 0,true)

def Canonical (L : List (V × Bool)) (ω : Set E) (i : ℕ) : Prop :=
  ∀ j z t, j < i → L[j]? = some z → L[i]? = some t →
    ¬(G.openGraph ω).Reachable z.1 t.1

noncomputable def owner (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) : ℕ := parent G (anchors d x n h) a ω none

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryMarks
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def nodeMark : (n : ℕ) → History E n → ℕ → Option E
  | 0, _, _ => none
  | n+1, h, i => if i = n+2 then h.2.2 else nodeMark n h.1 i

noncomputable def activeNodes (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) : Finset ℕ :=
  (historyForest G d x ω n h).active (owner G d x n h ω (x (interval d n h).1))
    (owner G d x n h ω (x (interval d n h).2))

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

def sides : (n : ℕ) → History E n → Fin n → Bool
  | 0, _ => Fin.elim0
  | n+1, h => Fin.snoc (sides n h.1) h.2.1

def marks : (n : ℕ) → History E n → Fin n → Option E
  | 0, _ => Fin.elim0
  | n+1, h => Fin.snoc (marks n h.1) h.2.2

def fromWords : (n : ℕ) → (Fin n → Bool) → (Fin n → Option E) → History E n
  | 0, _, _ => PUnit.unit
  | n+1, b, m => (fromWords n (Fin.init b) (Fin.init m),b (Fin.last n),m (Fin.last n))

lemma fromWords_sides_marks (n : ℕ) (h : History E n) :
    fromWords n (sides n h) (marks n h) = h := by
  induction n with
  | zero => cases h; rfl
  | succ n ih =>
    simp only [fromWords,sides,marks,Fin.init_snoc,Fin.snoc_last,ih]
    rfl

lemma sides_fromWords (n : ℕ) (b : Fin n → Bool) (m : Fin n → Option E) :
    sides n (fromWords n b m) = b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [fromWords,sides,ih,Fin.snoc_init_self]

lemma marks_fromWords (n : ℕ) (b : Fin n → Bool) (m : Fin n → Option E) :
    marks n (fromWords n b m) = m := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [fromWords,marks,ih,Fin.snoc_init_self]

def wordsEquiv (n : ℕ) : History E n ≃ (Fin n → Bool) × (Fin n → Option E) where
  toFun h := (sides n h, marks n h)
  invFun h := fromWords n h.1 h.2
  left_inv := fromWords_sides_marks n
  right_inv := fun h => Prod.ext (sides_fromWords n h.1 h.2) (marks_fromWords n h.1 h.2)

def historyPrefix : (n : ℕ) → History E n → (k : ℕ) → History E k
  | 0, _, 0 => PUnit.unit
  | 0, _, k+1 => fromWords (k+1) (fun _ => true) (fun _ => none)
  | n+1, h, k => if he : k = n+1 then he.symm ▸ h else historyPrefix n h.1 k

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedPivotWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def prefixScore (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r => (if openPivot F f ω then (1-p)*delta w F f else 0) +
      if e = f then 0 else
        if ω f then r.prefixScore p F (pin w f True) ω e
        else l.prefixScore p F (pin w f False) ω e

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_ReverseGuess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def reverseGuess (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) (e : E) : ℝ :=
  (if openPivot F e ω then (1-p)*T.queryDelta F w ω e else 0) /
    (1+s+T.prefixScore p F w ω e)^2

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation

universe u

inductive QueryTree (E : Type u) : Type u where
  | stop : QueryTree E
  | ask (e : E) (left right : QueryTree E) : QueryTree E

namespace QueryTree
variable {E : Type u}

@[reducible] def Leaf : QueryTree E → Type u
  | .stop => PUnit
  | .ask _ left right => Sum left.Leaf right.Leaf

def run : (t : QueryTree E) → (E → Bool) → t.Leaf
  | .stop, _ => PUnit.unit
  | .ask e left right, ω => if ω e then Sum.inr (right.run ω) else Sum.inl (left.run ω)

end QueryTree
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PushMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteEntropy
variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def pushMass (f : X → Y) (P : X → ℝ) (y : Y) : ℝ :=
  ∑ x, if f x = y then P x else 0

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BitWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

noncomputable def bitWeight (p : ℝ) (_ : E) (b : Bool) : ℝ := if b then p else 1-p

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Node
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
variable {E : Type*}

@[reducible] def Node : QueryTree E → Type
  | .stop => PEmpty
  | .ask _ l r => PUnit ⊕ (l.Node ⊕ r.Node)

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Uniform01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.Priority

noncomputable def uniform01 : Measure ℝ := volume.restrict (Icc 0 1)

instance instIsProbabilityMeasureRealUniform01 : IsProbabilityMeasure uniform01 := by
  constructor
  simp [uniform01, Real.volume_Icc]

end CriticalPercolation.Priority
open Set MeasureTheory Real
open scoped Interval

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_State
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

structure State (V E : Type*) where
  reached : Finset V
  read : Finset E

noncomputable def eligible (G : BondGraph V E) (st : State V E) (e : E) : Prop :=
  e ∉ st.read ∧ ∃ v ∈ st.reached, v ∈ G.ends e

noncomputable def closed (st : State V E) (e : E) : State V E :=
  ⟨st.reached, insert e st.read⟩

noncomputable def opened (G : BondGraph V E) (st : State V E) (e : E) : State V E :=
  ⟨st.reached ∪ (G.ends e).toFinset, insert e st.read⟩

noncomputable def compile (G : BondGraph V E) : ℕ → State V E → SearchTree E (State V E)
  | 0, st => .done st
  | n+1, st => if h : ∃ e, eligible G st e then
      let e := Classical.choose h
      .ask e (compile G n (closed st e)) (compile G n (opened G st e))
    else .done st

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Initial2
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

noncomputable def initial (S : Finset V) : State V E := ⟨S,∅⟩
noncomputable def search (G : BondGraph V E) (S : Finset V) : SearchTree E (State V E) :=
  compile G (Fintype.card E) (initial S)

noncomputable def pair (G : BondGraph V E) (a b : V) : SearchTree E (State V E) :=
  search G {a,b}

end CriticalPercolation.ExactExposure

namespace CriticalPercolation
namespace SearchTree
variable {E R : Type*}
def bare : SearchTree E R → QueryTree E
  | .done _ => .stop
  | .ask e l r => .ask e l.bare r.bare

end SearchTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClusterUsers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*}

def configuration (ω : E → Bool) : Set E := {e | ω e = true}

def Admissible (G : BondGraph V E) (B : Set V) (a b : V) (ω : E → Bool) (f : E) : Prop :=
  (¬∃ t ∈ B, (G.openGraph (configuration ω)).Reachable a t) ∧
    ∃ u v, G.ends f = s(u,v) ∧ (G.openGraph (configuration ω)).Reachable a u ∧
      (G.openGraph (configuration ω)).Reachable b v

variable [Fintype E]

variable [Fintype V]

noncomputable def markWeight (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Bool) (f : E) : ℝ :=
  if Admissible G B a b ω f then
    p * (LazyDFS.search G order a B).queryDelta
      (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f
  else 0

noncomputable def markCost (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Bool) (f : E) : ℝ :=
  if Admissible G B a b ω f then
    (LazyDFS.search G order a B).prefixScore p
      (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
      (Function.update (configuration ω) f True) f
  else 0

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryDescriptor
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest FiniteEntropy ExactExposure

variable {V E : Type*}

abbrev FixedDescriptor (n : ℕ) := Fin n → Bool × Bool × Bool

noncomputable def descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) : FixedDescriptor n := fun i =>
  (sides n h i, decide (marks n h i ≠ none), decide (i.val+2 ∈ activeNodes G d x n h ω))

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ)

noncomputable def jointMass (z : (E → Bool) × History E n) : ℝ :=
  FiniteProduct.density (QueryTree.bitWeight p) z.1 *
    density G order d x p w (seed G w (x 0) (x d) s) n z.2 (configuration z.1)

noncomputable def descriptorMass (D : FixedDescriptor n) : ℝ :=
  pushMass (fun z : (E → Bool) × History E n => descriptor G d x n z.2 (configuration z.1))
    (jointMass G order d x p w s n) D

noncomputable def fixedMass (D : FixedDescriptor n) (z : (E → Bool) × (Fin n → Option E)) : ℝ :=
  let h := fromWords n (fun i => (D i).1) z.2
  if descriptor G d x n h (configuration z.1) = D then
    jointMass G order d x p w s n (z.1,h) else 0

noncomputable def conditionedMass (D : FixedDescriptor n)
    (z : (E → Bool) × (Fin n → Option E)) : ℝ :=
  fixedMass G order d x p w s n D z / descriptorMass G order d x p w s n D

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryRaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

noncomputable def rawContact (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) : ℝ :=
  if a ∈ C.1 then if mark = none then 1 else 0 else
    match mark with
    | none => 0
    | some e => G.contactWeight order B C.1 a p w ω e

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

def scheduledAnchor (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool) (k : ℕ) : V :=
  x (nextIndex d k (historyPrefix n (fromWords n b (fun _ => (none : Option E))) k))

def scheduledTargets (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool) (k : ℕ) : Set V :=
  anchorSet d x k (historyPrefix n (fromWords n b (fun _ => (none : Option E))) k)

section Products
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

noncomputable def rawProduct : (n : ℕ) → History E n → (E → Prop) → ℝ
  | 0, _, _ => 1
  | n+1, h, ω => rawProduct n h.1 ω *
      G.rawContact order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
        (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2

noncomputable def scheduleWeight (n : ℕ) (b : Fin n → Bool)
    (i : Fin n) (ω : E → Prop) (m : Option E) : ℝ :=
  G.rawContact order (scheduledTargets (E := E) d x n b i.val)
    (scheduledAnchor (E := E) d x n b i.val) p w
    (G.clusterObject ω (scheduledTargets (E := E) d x n b i.val)) ω m

end Products
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_MarkedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]

noncomputable def logContactMass (a : I → X → M → ℝ) (ω : X) : ℝ :=
  ∑ i, Real.log (max 1 (∑ m, a i ω m))

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryConfiguration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation FiniteEntropy ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

noncomputable def constructionCost (c : ℝ) (s n : ℕ) (D : FixedDescriptor n) : ℝ :=
  Real.log ((prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n /
    descriptorMass G order d x p w s n D)

noncomputable section EntropyFinal
local instance classicalFinDecidable (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end EntropyFinal
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryParents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*}

def descriptorActive (n : ℕ) (D : FixedDescriptor n) : Finset ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => (D i).2.2 = true).image (fun i => i.val+2)

def descriptorNode (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ℕ) : V × Bool :=
  node d x n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none)) i

def descriptorParent (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => (j<2 ∨ j ∈ descriptorActive n D) ∧
    (descriptorNode (E := E) d x n D j).2 = (descriptorNode (E := E) d x n D i).2).sup id

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype I]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Bool)

abbrev ActiveIndex (n : ℕ) (D : FixedDescriptor n) := {i : Fin n // (D i).2.2 = true}

def activeLeft (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ActiveIndex n D) : V :=
  (descriptorNode (E := E) d x n D (i.val.val+2)).1

def activeRight (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ActiveIndex n D) : V :=
  (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val.val+2))).1

noncomputable section Entropy
local instance pairsClassicalFinDecidable (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end Entropy
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinarySwitches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph SearchTree BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def switched (n : ℕ) (h : History E n) (ω : Set E) (S : Finset ℕ) : Set E :=
  {e | ω e ∨ ∃ i ∈ S, nodeMark n h i = some e}

def targets (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) : Set V :=
  {v | ∃ j < i, (node d x n h j).1=v}

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*}

noncomputable def representative (f : X → Y) (x₀ : X) (y : Y) : X :=
  if h : ∃ x, f x = y then h.choose else x₀

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryTranscript
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*}

abbrev stepLeft (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : V :=
  (descriptorNode (E := E) d x n D (i.val+2)).1
abbrev stepRight (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : V :=
  (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val+2))).1
abbrev stepTargets (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : Set V :=
  scheduledTargets (E := E) d x n (fun j => (D j).1) i.val

def activeSteps (n : ℕ) (D : FixedDescriptor n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (D i).2.2 = true

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

noncomputable def pairQuery (i : Fin n) : QueryTree E :=
  (pair G (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i)).bare

noncomputable def selectedTranscript (i : Fin n) (ω : E → Bool) : E → Bool :=
  if (D i).2.2 = true then
    representative (pairQuery G d x n D i).run (fun _ => false) ((pairQuery G d x n D i).run ω)
  else ω

noncomputable def selectedWeight (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if (D i).2.2 = true then match m with
    | none => 0
    | some e => markWeight G order (stepTargets (E := E) d x n D i)
        (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i) p w ω e
  else scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m

noncomputable def selectedCost (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if (D i).2.2 = true then match m with
    | none => 0
    | some e => markCost G order (stepTargets (E := E) d x n D i)
        (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i) p w ω e
  else 0

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryInverseCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

noncomputable section Cost
local instance inverseCostFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end Cost
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ReverseReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.ReverseReference
open scoped Classical

variable {X M : Type*} [Fintype M]

noncomputable def weight (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) :
    (n : ℕ) → X → (Fin n → M) → ℝ
  | 0, _, _ => 1
  | n+1, x, m => k n x (m (Fin.last n)) *
    weight k u n (u n x (m (Fin.last n))) (Fin.init m)

def recover (u : ℕ → X → M → X) : (n : ℕ) → X → (Fin n → M) → X
  | 0, x, _ => x
  | n+1, x, m => recover u n (u n x (m (Fin.last n))) (Fin.init m)

section Terminal
variable [Fintype X] {I : Type*} [Fintype I]

noncomputable def terminalWeight (a : I → X → M → ℝ) (x : X) (m : I → M) : ℝ :=
  ∏ i, a i x (m i)

noncomputable def joint (μ : X → ℝ) (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (a : I → X → M → ℝ) (n : ℕ) (z : X × (Fin n → M) × (I → M)) : ℝ :=
  μ z.1 * weight k u n z.1 z.2.1 * terminalWeight a (recover u n z.1 z.2.1) z.2.2

end Terminal
end CriticalPercolation.ReverseReference

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_MarkedBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.MarkedBits
open scoped Classical
open FiniteProduct ExactExposure

variable {E I : Type*}

noncomputable def opened (S : Finset I) (m : I → Option E) (ω : E → Bool) : E → Bool :=
  fun e => if ∃ i ∈ S, m i = some e then true else ω e

noncomputable def masked (S : Finset I) (m : I → Option E) : I → Option E :=
  fun i => if i ∈ S then m i else none

end CriticalPercolation.MarkedBits

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryReverseKernels
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance kernelsFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

noncomputable def pivotGuess (i : Fin n) (ω : E → Bool) (e : E) : ℝ :=
  (LazyDFS.search G order (stepLeft (E := E) d x n D i) (stepTargets (E := E) d x n D i)).reverseGuess
    p (fun σ => ∃ b ∈ stepTargets (E := E) d x n D i,
      (G.openGraph σ).Reachable (stepLeft (E := E) d x n D i) b) w (configuration ω) 0 e

noncomputable def inverseKernel (j : ℕ) (ω : E → Bool) (m : Option E) : ℝ :=
  if hj : j < n then
    if (⟨j,hj⟩ : Fin n) ∈ activeSteps n D then
      match m with | none => 0 | some e => pivotGuess G order d x p w n D ⟨j,hj⟩ ω e
    else if m = none then 1 else 0
  else if m = none then 1 else 0

noncomputable def inverseUpdate (j : ℕ) (ω : E → Bool) (m : Option E) : E → Bool :=
  if hj : j < n then
    if (⟨j,hj⟩ : Fin n) ∈ activeSteps n D then
      match m with | none => ω | some e => Function.update ω e false
    else ω
  else ω

noncomputable def contactTotal (i : Fin n) (ω : E → Bool) : ℝ :=
  ∑ m, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m

noncomputable def inactiveKernel (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if i ∈ activeSteps n D then if m=none then 1 else 0
  else if contactTotal G order d x p w n D i ω = 0 then if m=none then 1 else 0
  else scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m /
    contactTotal G order d x p w n D i ω

noncomputable def inverseReference : ((E → Bool) × (Fin n → Option E) × (Fin n → Option E)) → ℝ :=
  ReverseReference.joint (FiniteProduct.density (QueryTree.bitWeight p))
    (inverseKernel G order d x p w n D) (inverseUpdate (E := E) n D)
    (inactiveKernel G order d x p w n D) n

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryOutput
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph LazyDFS BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def HasSide (L : List (V × Bool)) (ω : Set E) (b : Bool) (v : V) : Prop :=
  ∃ z ∈ L, z.2=b ∧ (G.openGraph ω).Reachable z.1 v

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*}
local instance stagesFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

noncomputable def stageIndices (n : ℕ) (D : FixedDescriptor n) (k : ℕ) : Finset (Fin n) :=
  (activeSteps n D).filter fun i => i.val < k

noncomputable def stage (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool)
    (m : Fin n → Option E) (k : ℕ) : E → Bool := opened (stageIndices n D k) m ω

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryReversePrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance pricesFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryLikelihood
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance likelihoodFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

def inversePenalty (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  (if i ∈ activeSteps n D then (1+selectedCost G order d x p w n D i ω m)^2 else 1) *
    max 1 (contactTotal G order d x p w n D i ω)

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryReferenceLikelihood
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance refLikelihoodFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

noncomputable def recorded (n : ℕ) (D : FixedDescriptor n) (z : (E → Bool) × (Fin n → Option E)) :
    (E → Bool) × (Fin n → Option E) × (Fin n → Option E) :=
  (stage n D z.1 z.2 n,masked (activeSteps n D) z.2,masked (activeSteps n D)ᶜ z.2)

variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

def inverseLog (ω : E → Bool) (m : Fin n → Option E) : ℝ :=
  2*(∑ i ∈ activeSteps n D, Real.log (1+selectedCost G order d x p w n D i ω (m i))) +
    logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration ω)

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryOutputEntropy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
local instance outputEntropyFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

noncomputable def outputMass : (E → Bool) → ℝ :=
  pushMass (fun z => stage n D z.1 z.2 n) (conditionedMass G order d x p w s n D)

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryEventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
local instance eventBoundFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteInterpolation
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E]

local instance interpolationFinDec_r189ff3_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
def allDarts (G : BondGraph V E) : List (LazyDFS.Dart V E) :=
  (Finset.univ.filter (fun a : LazyDFS.Dart V E => G.ends a.2.1 = s(a.1,a.2.2))).toList

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteInterpolationMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def twoClusterEvent (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.openGraph ω).Reachable u v} ∩ G.clusterTail u s ∩ G.clusterTail v s

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_WitnessEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def witnessedTwoCluster (K : Set E) (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.openGraph ω).Reachable u v} ∩
    {ω | K∩ω ∈ G.clusterTail u s ∩ G.clusterTail v s}

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteInduced
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def inducedEdges (S : Set V) : Set E := {e | ∀ v ∈ G.ends e, v∈S}

def induce (S : Set V) : BondGraph S (G.inducedEdges S) where
  ends e := (G.ends e.val).attachWith e.property

lemma induce_ends_map (S : Set V) (e : G.inducedEdges S) :
    Sym2.map Subtype.val ((G.induce S).ends e) = G.ends e.val :=
  Sym2.attachWith_map_subtypeVal _

lemma induce_ends_eq (S : Set V) (e : G.inducedEdges S) (u v : S) :
    (G.induce S).ends e = s(u,v) ↔ G.ends e.val = s(u.val,v.val) := by
  rw [← G.induce_ends_map S e,← Sym2.map_mk]
  exact (Sym2.map.injective Subtype.val_injective).eq_iff.symm

lemma finite_incident (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.incidentEdges S).Finite := by
  have hh := hS.biUnion (fun v _ => hG v)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext e
  simp only [incidentEdges,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]

lemma finite_inducedEdges (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.inducedEdges S).Finite := by
  apply (G.finite_incident hG hS).subset
  intro e he
  obtain ⟨⟨u,v⟩,huv⟩ := Sym2.mk_surjective (G.ends e)
  have hu : u ∈ G.ends e := by rw [← huv]; simp
  exact ⟨u,he u hu,hu⟩

lemma induce_adj (S : Set V) (ω : Set (G.inducedEdges S)) (u v : S) :
    ((G.induce S).openGraph ω).Adj u v ↔
      (G.openGraph (Subtype.val '' ω)).Adj u.val v.val := by
  simp only [openGraph,SimpleGraph.fromEdgeSet_adj,Set.mem_image]
  constructor
  · rintro ⟨⟨e,he,hend⟩,hne⟩
    exact ⟨⟨e.val,⟨e,he,rfl⟩,(G.induce_ends_eq S e u v).mp hend⟩,
      fun h => hne (Subtype.ext h)⟩
  · rintro ⟨⟨e,⟨a,ha,rfl⟩,hend⟩,hne⟩
    exact ⟨⟨a,ha,(G.induce_ends_eq S a u v).mpr hend⟩,
      fun h => hne (congrArg Subtype.val h)⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BallIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_bond_endpoints {K : Set E} (hK : K.Finite) :
    (⋃ e∈K, {v | v∈G.ends e}).Finite := by
  apply hK.biUnion
  intro e _
  convert (G.ends e).toFinset.finite_toSet using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  exact Sym2.mem_toFinset.symm

lemma finite_bonds_in_ball (hconnected : G.fullGraph.Connected) (o : V)
    {K : Set E} (hK : K.Finite) : ∃ W, K ⊆ G.inducedEdges (G.vertexBall o W) := by
  obtain ⟨W,hW⟩ := G.finite_subset_vertexBall hconnected o (G.finite_bond_endpoints hK)
  refine ⟨W,?_⟩
  intro e he v hv
  exact hW (Set.mem_iUnion₂.mpr ⟨e,he,hv⟩)

lemma inducedEdges_monotone : Monotone G.inducedEdges := by
  intro S T h e he v hv
  exact h (he v hv)

def inducedBallExhaustion (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (o : V) : Set.FiniteExhaustion (Set.univ : Set E) where
  toFun n := G.inducedEdges (G.vertexBall o n)
  finite' n := G.finite_inducedEdges hlocal (G.vertexBall_finite hlocal o n)
  subset_succ' n := G.inducedEdges_monotone (G.vertexBall_mono o (Nat.le_succ n))
  iUnion_eq' := by
    apply Set.eq_univ_of_forall
    intro e
    obtain ⟨W,hW⟩ := G.finite_bonds_in_ball hconnected o (Set.finite_singleton e)
    exact Set.mem_iUnion.mpr ⟨W,hW rfl⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_UniformGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

protected def Aut.symm (φ : G.Aut) : G.Aut where
  vertex := φ.vertex.symm
  edge := φ.edge.symm
  preserves e := by
    have h := φ.preserves (φ.edge.symm e)
    have hh := congrArg (Sym2.map φ.vertex.symm) h
    simpa only [Equiv.apply_symm_apply,Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id',id_eq] using hh.symm

protected def Aut.trans (φ ψ : G.Aut) : G.Aut where
  vertex := φ.vertex.trans ψ.vertex
  edge := φ.edge.trans ψ.edge
  preserves e := by
    simp only [Equiv.trans_apply,ψ.preserves,φ.preserves,Sym2.map_map]
    rfl

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

noncomputable def clusterSize (ω : Set E) (v : V) : ℕ :=
  (G.cluster ω v).toFinset.card

noncomputable def rootMass (f : ℕ → ℝ) (ω : Set E) (v : V) : ℝ :=
  f (G.clusterSize ω v) / G.clusterSize ω v

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_CappedDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

namespace BondGraph
open FiniteProduct

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

def edgeClusterMass (f : ℕ → ℝ) (ω : Set E) (e : E) : ℝ :=
  ∑ v, if e ∈ G.incidentEdges (G.cluster ω v) then G.rootMass f ω v else 0

variable [Fintype E]

def clusterDiscrepancy (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  ∑ e, if e ∈ G.incidentEdges (G.cluster ω v) then (if ω e then -(1-p)/p else 1) else 0

def edgeDiscrepancy (f : ℕ → ℝ) (p : ℝ) (ω : Set E) (e : E) : ℝ :=
  (if ω e then -(1-p)/p else 1) * G.edgeClusterMass f ω e

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_InfiniteUniquenessGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def distinctInfiniteEvent (x y : V) : Set (Set E) :=
  {ω | (G.cluster ω x).Infinite ∧ (G.cluster ω y).Infinite ∧
    ¬ (G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_InfiniteUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def atMostOneInfinite : Set (Set E) :=
  {ω | ∀ x y, (G.cluster ω x).Infinite → (G.cluster ω y).Infinite →
    (G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_FiniteClusterCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def infiniteClusterCover (ω : Set E) (S : Set V) : Prop :=
  ∀ v, (G.cluster ω v).Infinite → ∃ s ∈ S, (G.openGraph ω).Reachable v s

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_FreshTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def allOpen (F : Set E) : Set (Set E) := {ω | F⊆ω}

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BlockIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

def closedBlock (S : Set E) : Set (Set E) := {ω | Disjoint S ω}

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_CylinderApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def finiteCoordinateEvents : Set (Set (Set E)) :=
  {A | ∃ S : Finset E, MeasurableSet[blockSigma (S : Set E)] A}

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def infinitelyManyInfiniteClusters (ω : Set E) : Prop :=
  ∀ S : Finset V, ∃ v, (G.cluster ω v).Infinite ∧
    ∀ s ∈ S, ¬ (G.openGraph ω).Reachable v s

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ConditionalGluing
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def seedHitEvent (B T : Set V) : Set (Set E) :=
  ⋃ b∈B, G.hitEvent b T

lemma measurableSet_seedHitEvent [Countable V] [Countable E] (B T : Set V) :
    MeasurableSet (G.seedHitEvent B T) :=
  MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => G.measurableSet_hitEvent b T

def goodRelay (q : E → unitInterval) (S : Set E) (L : Set V)
    (F : V → Set E) (B : V → Set V) (T : Set V) (lam : ℝ) (σ : Set E) : Set V :=
  {v | v∈L ∧ F v⊆σ ∧ 1-lam≤(blockProbability q S (G.seedHitEvent (B v) T) σ).toReal}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CollarDistance
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def vertexCollar (B : Set V) (n : ℕ) : Set V := ⋃ b∈B, G.vertexBall b n

def distanceTo (B : Set V) (v : V) : ℕ :=
  if h : ∃ n, v∈G.vertexCollar B n then Nat.find h else 0

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Corridor

abbrev Site := ℤ×ℤ
abbrev Point := ℝ×ℝ
abbrev Edge := Site×Bool

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_RelayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Relay

def width (i : ℕ) : ℝ := max 2 (210-(i : ℝ)/2)

def domain (J T σ : ℝ) : Set (ℝ×ℝ) :=
  {x | |x.1| ≤ J ∧ |x.2| ≤ J/4+630} ∪
  {x | |x.1-T| ≤ J ∧ |x.2-σ*T/4| ≤ J/4+630} ∪
  {x | 0 ≤ x.1 ∧ x.1 ≤ T ∧ |x.2-σ*x.1/4| ≤ 630}

end CriticalPercolation.Relay
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_RelayMoves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma open_induced_adj (S : Set V) (ω : Set E) (u v : V) :
    (G.openGraph (ω∩G.inducedEdges S)).Adj u v ↔
    (G.openGraph ω).Adj u v ∧ u∈S ∧ v∈S := by
  constructor
  · rintro ⟨⟨b,hb,hend⟩,hne⟩
    exact ⟨⟨⟨b,hb.1,hend⟩,hne⟩,hb.2 u (by rw [hend]; simp),
      hb.2 v (by rw [hend]; simp)⟩
  · rintro ⟨⟨⟨b,hb,hend⟩,hne⟩,hu,hv⟩
    refine ⟨⟨b,⟨hb,?_⟩,hend⟩,hne⟩
    intro w hw
    rw [hend] at hw
    rcases (Sym2.mem_iff.mp hw) with rfl|rfl <;> assumption

def coordinateMove (t z : V → ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.vertexBall y m, ∃ b, ∃ w : (G.openGraph ω).Walk a b,
    (∀ x∈w.support, |t x-t y| ≤ 100 ∧ |z x-z y| ≤ 100) ∧
    |t b-(t y+1)| ≤ e/4 ∧ |z b-(z y+s)| ≤ e/4}

def relayRegion (t z : V → ℝ) (σ e : ℝ) (i : ℕ) : Set V :=
  {v | |t v-(i : ℝ)| ≤ (i+1)*e ∧ |z v-σ*(i : ℝ)/4| ≤ Relay.width i}

def relayMark (t z : V → ℝ) (T σ ρ : ℝ) : Set V :=
  {v | T ≤ t v ∧ t v ≤ T+ρ ∧ |z v-σ*T/4| ≤ 210}

def relayDomain (t z : V → ℝ) (J T σ : ℝ) : Set V :=
  (fun v => (t v,z v)) ⁻¹' Relay.domain J T σ

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[ext] lemma Aut.ext {f g : G.Aut} (hv : f.vertex=g.vertex) (he : f.edge=g.edge) : f=g := by
  cases f
  cases g
  cases hv
  cases he
  rfl

instance instGroupAut : Group G.Aut where
  one := ⟨Equiv.refl V,Equiv.refl E,by intro e; simp⟩
  mul f g := Aut.trans G g f
  inv f := Aut.symm G f
  mul_assoc f g h := by apply Aut.ext G <;> rfl
  one_mul f := by apply Aut.ext G <;> rfl
  mul_one f := by apply Aut.ext G <;> rfl
  inv_mul_cancel f := by
    apply Aut.ext G <;> apply Equiv.ext <;> intro x <;>
      exact Equiv.symm_apply_apply _ x

instance instMulActionAut : MulAction G.Aut V where
  smul f x := f.vertex x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma Aut.smul_vertex (f : G.Aut) (x : V) : f • x=f.vertex x := rfl

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RelativeModular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace Subgroup
open scoped _root_.Subgroup
variable {Γ : Type*} [Group Γ]

def relativeMass (A B : Subgroup Γ) : ℝ := (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

lemma relativeMass_eq_of_le {I A B : Subgroup Γ} (hIA : I ≤ A) (hIB : I ≤ B)
    (hI : I.relIndex A ≠ 0) :
    relativeMass A B = (I.relIndex A : ℝ) / (I.relIndex B : ℝ) := by
  have ha := _root_.Subgroup.relIndex_mul_relIndex I (A ⊓ B) A (le_inf hIA hIB) inf_le_left
  have hb := _root_.Subgroup.relIndex_mul_relIndex I (A ⊓ B) B (le_inf hIA hIB) inf_le_right
  have hi : I.relIndex (A ⊓ B) ≠ 0 := by
    intro hi
    rw [hi,zero_mul] at ha
    exact hI ha.symm
  have hir : (I.relIndex (A ⊓ B) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  rw [_root_.Subgroup.inf_relIndex_left] at ha
  rw [_root_.Subgroup.inf_relIndex_right] at hb
  unfold relativeMass
  calc
    _ = ((I.relIndex (A ⊓ B) : ℝ) * (B.relIndex A : ℝ)) /
        ((I.relIndex (A ⊓ B) : ℝ) * (A.relIndex B : ℝ)) :=
      (mul_div_mul_left _ _ hir).symm
    _ = _ := by simp only [← Nat.cast_mul,ha,hb]

lemma relativeMass_cocycle (A B C : Subgroup Γ)
    (hab : A.relIndex B ≠ 0) (hba : B.relIndex A ≠ 0)
    (hca : C.relIndex A ≠ 0) (hcb : C.relIndex B ≠ 0) :
    relativeMass A B * relativeMass B C = relativeMass A C := by
  let I := A ⊓ B ⊓ C
  have hIA : I ≤ A := inf_le_left.trans inf_le_left
  have hIB : I ≤ B := inf_le_left.trans inf_le_right
  have hIC : I ≤ C := inf_le_right
  have hI0A : I.relIndex A ≠ 0 :=
    _root_.Subgroup.relIndex_inf_ne_zero (by simpa only [_root_.Subgroup.inf_relIndex_left] using hba) hca
  have hI0B : I.relIndex B ≠ 0 :=
    _root_.Subgroup.relIndex_inf_ne_zero (by simpa only [_root_.Subgroup.inf_relIndex_right] using hab) hcb
  rw [relativeMass_eq_of_le hIA hIB hI0A,relativeMass_eq_of_le hIB hIC hI0B,
    relativeMass_eq_of_le hIA hIC hI0A]
  exact div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr hI0B)

end Subgroup
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_GraphModular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stabilizerOrbit (x y : V) : Set V :=
  MulAction.orbit (MulAction.stabilizer G.Aut x) y

lemma mem_stabilizerOrbit {x y z : V} : z ∈ G.stabilizerOrbit x y ↔
    ∃ φ : G.Aut, φ.vertex x = x ∧ φ.vertex y = z := by
  simp only [stabilizerOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨φ,hφ⟩
    exact ⟨φ,φ.property,hφ⟩
  · rintro ⟨φ,hx,hy⟩
    exact ⟨⟨φ,hx⟩,hy⟩

lemma self_mem_stabilizerOrbit (x y : V) : y ∈ G.stabilizerOrbit x y :=
  (G.mem_stabilizerOrbit).mpr ⟨1,rfl,rfl⟩

lemma stabilizerOrbit_finite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : (G.stabilizerOrbit x y).Finite := by
  obtain ⟨n,hn⟩ := G.finite_subset_vertexBall hc x (Set.finite_singleton y)
  apply (G.vertexBall_finite hl x n).subset
  intro z hz
  obtain ⟨φ,hx,rfl⟩ := G.mem_stabilizerOrbit.mp hz
  rw [←hx]
  exact (Aut.vertexBall_mem G φ x y n).mpr (hn (Set.mem_singleton y))

def suborbitCard (x y : V) : ℕ := (G.stabilizerOrbit x y).ncard

lemma suborbitCard_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : 0 < G.suborbitCard x y :=
  (Set.ncard_pos (G.stabilizerOrbit_finite hc hl x y)).mpr ⟨y,G.self_mem_stabilizerOrbit x y⟩

lemma suborbitCard_eq_relIndex (x y : V) : G.suborbitCard x y =
    (MulAction.stabilizer G.Aut y).relIndex (MulAction.stabilizer G.Aut x) := by
  have heq : (MulAction.stabilizer G.Aut y).subgroupOf (MulAction.stabilizer G.Aut x) =
      MulAction.stabilizer (MulAction.stabilizer G.Aut x) y := by
    ext φ
    rfl
  rw [Subgroup.relIndex,heq,MulAction.index_stabilizer]
  rfl

lemma Aut.stabilizerOrbit_image (φ : G.Aut) (x y : V) :
    φ.vertex '' G.stabilizerOrbit x y = G.stabilizerOrbit (φ.vertex x) (φ.vertex y) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨ψ,hx,hy⟩ := G.mem_stabilizerOrbit.mp hw
    apply G.mem_stabilizerOrbit.mpr
    refine ⟨φ * ψ * φ⁻¹,?_,?_⟩
    · change φ.vertex (ψ.vertex (φ.vertex.symm (φ.vertex x))) = φ.vertex x
      rw [Equiv.symm_apply_apply,hx]
    · change φ.vertex (ψ.vertex (φ.vertex.symm (φ.vertex y))) = φ.vertex w
      rw [Equiv.symm_apply_apply,hy]
  · intro hz
    obtain ⟨ψ,hx,hy⟩ := G.mem_stabilizerOrbit.mp hz
    refine ⟨φ.vertex.symm z,?_,φ.vertex.apply_symm_apply z⟩
    apply G.mem_stabilizerOrbit.mpr
    refine ⟨φ⁻¹ * ψ * φ,?_,?_⟩
    · change φ.vertex.symm (ψ.vertex (φ.vertex x)) = x
      rw [hx,Equiv.symm_apply_apply]
    · change φ.vertex.symm (ψ.vertex (φ.vertex y)) = φ.vertex.symm z
      rw [hy]

lemma Aut.suborbitCard (φ : G.Aut) (x y : V) :
    G.suborbitCard (φ.vertex x) (φ.vertex y) = G.suborbitCard x y := by
  rw [CriticalPercolation.BondGraph.suborbitCard,←Aut.stabilizerOrbit_image G φ,
      Set.ncard_image_of_injective _ φ.vertex.injective]
  rfl

def modularRatio (x y : V) : ℝ := (G.suborbitCard x y : ℝ) / (G.suborbitCard y x : ℝ)

lemma modularRatio_eq_relativeMass (x y : V) : G.modularRatio x y =
    Subgroup.relativeMass (MulAction.stabilizer G.Aut x) (MulAction.stabilizer G.Aut y) := by
  simp only [modularRatio,suborbitCard_eq_relIndex,Subgroup.relativeMass]

lemma modularRatio_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    0 < G.modularRatio x y :=
  div_pos (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl x y))
    (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x))

lemma modularRatio_cocycle (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y z : V) : G.modularRatio x y * G.modularRatio y z = G.modularRatio x z := by
  simp only [modularRatio_eq_relativeMass]
  apply Subgroup.relativeMass_cocycle
  all_goals
    rw [←suborbitCard_eq_relIndex]
    exact ne_of_gt (G.suborbitCard_pos hc hl _ _)

lemma Aut.modularRatio (φ : G.Aut) (x y : V) :
    G.modularRatio (φ.vertex x) (φ.vertex y) = G.modularRatio x y := by
  simp only [CriticalPercolation.BondGraph.modularRatio,Aut.suborbitCard]

def CombinatoriallyUnimodular : Prop :=
  ∀ (φ : G.Aut) x, G.suborbitCard x (φ.vertex x) = G.suborbitCard (φ.vertex x) x

lemma CombinatoriallyUnimodular.modularRatio (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (φ : G.Aut) (x : V) :
    G.modularRatio x (φ.vertex x) = 1 := by
  simp only [CriticalPercolation.BondGraph.modularRatio,hu φ x,
    div_self (ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl (φ.vertex x) x)) :
      (G.suborbitCard (φ.vertex x) x : ℝ) ≠ 0)]

lemma CombinatoriallyUnimodular.rootWeight_invariant (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (o : V) (φ : G.Aut) (x : V) :
    G.modularRatio o (φ.vertex x) = G.modularRatio o x := by
  rw [← G.modularRatio_cocycle hc hl o (φ.vertex o) (φ.vertex x),
    CombinatoriallyUnimodular.modularRatio G hu hc hl φ o,one_mul,Aut.modularRatio]

lemma modularRatio_card_balance (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x y : V) : G.modularRatio o x * (G.suborbitCard x y : ℝ) =
      G.modularRatio o y * (G.suborbitCard y x : ℝ) := by
  have hh := G.modularRatio_cocycle hc hl o x y
  unfold modularRatio at hh
  rw [← mul_div_assoc] at hh
  exact (div_eq_iff (ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x)))).mp hh

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularClusterMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stabilizerWeight (o x : V) : ℝ≥0∞ := ENNReal.ofReal (G.modularRatio x o)

def modularMass (o : V) (S : Set V) : ℝ≥0∞ :=
  ∑' x : V, if x∈S then G.stabilizerWeight o x else 0

def lightInfiniteEvent (o v : V) : Set (Set E) :=
  {ω | (G.cluster ω v).Infinite ∧ G.modularMass o (G.cluster ω v) < ∞}

def heavyClusterEvent (o v : V) : Set (Set E) :=
  {ω | G.modularMass o (G.cluster ω v) = ∞}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyHarris
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def massTailEvent (o v : V) (a : ℝ≥0∞) : Set (Set E) :=
  {ω | a<G.modularMass o (G.cluster ω v)}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DescendingFan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def weightCeiling (v : V) (K : ℝ≥0∞) : Set V := {x | G.stabilizerWeight v x≤K}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_SuperpolynomialRadius
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def SuperpolynomialGrowth : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n≥N, ∀ v : V, n^M≤(G.vertexBall v n).ncard

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_GrowthAlternatives
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def maxVolume (n : ℕ) : ℕ := sSup (Set.range fun v => (G.vertexBall v n).ncard)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyClusterNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def atMostOneHeavy (o : V) : Set (Set E) :=
  {ω | ∀ x y, G.modularMass o (G.cluster ω x) = ∞ →
    G.modularMass o (G.cluster ω y) = ∞ → (G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakClusters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterPeak (ω : Set E) (x : V) : Prop :=
  ∀ z, (G.openGraph ω).Reachable x z → G.stabilizerWeight x z ≤ 1

def clusterPeaks (ω : Set E) (v : V) : Set V :=
  {x | (G.openGraph ω).Reachable v x ∧ G.clusterPeak ω x}

def peakBound (N : ℕ) (ω : Set E) (v : V) : Prop :=
  ∃ S : Finset V, S.card ≤ N ∧ G.clusterPeaks ω v ⊆ S

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularSuperlevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterUpperSet (ω : Set E) (v : V) : Set V :=
  {x | x ∈ G.cluster ω v ∧ 1 ≤ G.stabilizerWeight v x}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakRatioTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def peakRatioTransport (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y∈G.clusterPeaks ω x then
    (G.modularMass y (G.cluster ω x))⁻¹ * ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹
  else 0

def clusterPeakRatio (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.peakRatioTransport ω x y

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularClusterCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def reciprocalClusterMass (ω : Set E) (x : V) : ℝ≥0∞ :=
  (G.modularMass x (G.cluster ω x))⁻¹

def finiteMassIndicator (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.modularMass x (G.cluster ω x)=∞ then 0 else 1

def incidentClusterCount (ω : Set E) (e : E) : ℝ≥0∞ :=
  ∑' x, if e∈G.incidentEdges (G.cluster ω x) then G.reciprocalClusterMass ω x else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def bondWeight (o : V) (e : E) : ℝ≥0∞ := ∑ v ∈ (G.ends e).toFinset, G.stabilizerWeight o v

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure OrbitRepresentatives where
  roots : Finset V
  cover : ∀ x : V, ∃ u ∈ roots, ∃ φ : G.Aut, φ.vertex u = x
  unique : ∀ u ∈ roots, ∀ v ∈ roots, ∀ φ : G.Aut, φ.vertex u = v → u = v

lemma finite_vertexOrbits (hq : G.QuasiTransitive) :
    Finite (MulAction.orbitRel.Quotient G.Aut V) := by
  obtain ⟨S,hS,hcover⟩ := hq
  apply Set.finite_univ_iff.mp
  apply (hS.image (fun x : V => (Quotient.mk'' x : MulAction.orbitRel.Quotient G.Aut V))).subset
  intro q _
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨u,hu,φ,hφ⟩ := hcover x
    refine ⟨u,hu,?_⟩
    apply Quotient.sound
    exact MulAction.mem_orbit_symm.mpr (MulAction.mem_orbit_iff.mpr ⟨φ,hφ⟩)

def orbitRepresentatives (hq : G.QuasiTransitive) : G.OrbitRepresentatives := by
  letI := G.finite_vertexOrbits hq
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient G.Aut V)
  let S : Finset V := Finset.univ.image (Quotient.out : MulAction.orbitRel.Quotient G.Aut V → V)
  refine ⟨S,?_,?_⟩
  · intro x
    let q : MulAction.orbitRel.Quotient G.Aut V := Quotient.mk'' x
    refine ⟨q.out,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩
    have heq : (Quotient.mk'' q.out : MulAction.orbitRel.Quotient G.Aut V) = Quotient.mk'' x := q.out_eq'
    exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp (Quotient.exact heq))
  · intro u hu v hv φ hφ
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
    have heq : (Quotient.mk'' r.out : MulAction.orbitRel.Quotient G.Aut V) = Quotient.mk'' q.out :=
      Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨φ,hφ⟩)
    rw [Quotient.out_eq',Quotient.out_eq'] at heq
    exact congrArg Quotient.out heq.symm

abbrev PairOrbit := MulAction.orbitRel.Quotient G.Aut (V × V)

def pairOrbit (x y : V) : G.PairOrbit := Quotient.mk'' (x,y)

lemma pairOrbit_eq {x y u v : V} : G.pairOrbit x y = G.pairOrbit u v ↔
    ∃ φ : G.Aut, φ.vertex x = u ∧ φ.vertex y = v := by
  constructor
  · intro h
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
    exact ⟨φ,congrArg Prod.fst hφ,congrArg Prod.snd hφ⟩
  · rintro ⟨φ,hx,hy⟩
    apply Eq.symm
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext hx hy⟩

lemma Aut.pairOrbit (φ : G.Aut) (x y : V) :
    G.pairOrbit (φ.vertex x) (φ.vertex y) = G.pairOrbit x y :=
  (G.pairOrbit_eq.mpr ⟨φ,rfl,rfl⟩).symm

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

abbrev RootedPair := {x // x ∈ R.roots} × V

def pairMap (p : R.RootedPair) : G.PairOrbit := G.pairOrbit p.1 p.2

lemma fiber_root_eq (x : {x // x∈R.roots}) (y : V)
    (p : (pairMap G R) ⁻¹' {G.pairOrbit x y}) : p.val.1 = x := by
  have hh : G.pairOrbit (x:V) y = G.pairOrbit (p.val.1:V) p.val.2 := p.property.symm
  obtain ⟨φ,hφ,_⟩ := G.pairOrbit_eq.mp hh
  exact Subtype.ext (R.unique x x.property p.val.1 p.val.1.property φ hφ).symm

lemma fiber_snd_mem (x : {x // x∈R.roots}) (y : V)
    (p : (pairMap G R) ⁻¹' {G.pairOrbit x y}) : p.val.2 ∈ G.stabilizerOrbit x y := by
  have hh : G.pairOrbit (x:V) y = G.pairOrbit (p.val.1:V) p.val.2 := p.property.symm
  obtain ⟨φ,hφ,hy⟩ := G.pairOrbit_eq.mp hh
  exact G.mem_stabilizerOrbit.mpr ⟨φ,by rw [hφ,fiber_root_eq G R x y p],hy⟩

def fiberEquiv (x : {x // x∈R.roots}) (y : V) :
    (pairMap G R) ⁻¹' {G.pairOrbit x y} ≃ G.stabilizerOrbit x y where
  toFun p := ⟨p.val.2,fiber_snd_mem G R x y p⟩
  invFun z := ⟨(x,z),by
    obtain ⟨φ,hx,hz⟩ := G.mem_stabilizerOrbit.mp z.property
    exact (G.pairOrbit_eq.mpr ⟨φ,hx,hz⟩).symm⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (fiber_root_eq G R x y p).symm rfl
  right_inv z := rfl

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_OrbitalMassTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def swapPairOrbitFn : G.PairOrbit → G.PairOrbit :=
  Quotient.map Prod.swap (by
    intro a b hab
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp hab
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext (congrArg Prod.snd hφ) (congrArg Prod.fst hφ)⟩)

def swapPairOrbit : G.PairOrbit ≃ G.PairOrbit where
  toFun := swapPairOrbitFn G
  invFun := swapPairOrbitFn G
  left_inv q := by induction q using Quotient.inductionOn' with | h p => rfl
  right_inv q := by induction q using Quotient.inductionOn' with | h p => rfl

@[simp] lemma swapPairOrbit_mk (x y : V) :
    G.swapPairOrbit (G.pairOrbit x y) = G.pairOrbit y x := rfl

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

def weightedRow (w : V → ℝ) (F : V → V → ℝ) (p : R.RootedPair) : ℝ :=
  w p.1 * F p.1 p.2

lemma weightedRow_finite (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ x, (Function.support (F x)).Finite) :
    (Function.support (weightedRow G R w F)).Finite := by
  apply (Set.finite_iUnion (fun x : {x // x∈R.roots} =>
    (hF x).image (Prod.mk x))).subset
  intro p hp
  refine Set.mem_iUnion.mpr ⟨p.1,p.2,?_,rfl⟩
  intro hz
  exact hp (by simp only [weightedRow,hz,mul_zero])

lemma fiber_sum_root (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x : {x // x∈R.roots}) (y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, weightedRow G R w F p) =
      w x * (G.suborbitCard x y : ℝ) * F x y := by
  let := (G.stabilizerOrbit_finite hc hl x y).fintype
  rw [← (fiberEquiv G R x y).symm.tsum_eq]
  have hv (z : G.stabilizerOrbit x y) :
      weightedRow G R w F ((fiberEquiv G R x y).symm z) = w x * F x y := by
    change w x * F x z = w x * F x y
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp z.property
    have hh := hF φ x y
    rw [hx,hy] at hh
    rw [hh]
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (G.stabilizerOrbit x y) = G.suborbitCard x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]
  ring

lemma fiber_sum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (hw : ∀ (φ : G.Aut) x, w (φ.vertex x) = w x)
    (F : V → V → ℝ) (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, weightedRow G R w F p) =
      w x * (G.suborbitCard x y : ℝ) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ.vertex.symm y
  have hy : φ.vertex v = y := φ.vertex.apply_symm_apply y
  have hq : G.pairOrbit (φ.vertex u) y = G.pairOrbit u v := by
    rw [←hy,Aut.pairOrbit]
  rw [hq,fiber_sum_root G R hc hl w F hF ⟨u,hu⟩ v]
  change w u * (G.suborbitCard u v : ℝ) * F u v = _
  rw [←hy,hw,Aut.suborbitCard,hF]

lemma tsum_weightedRow (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ x, (Function.support (F x)).Finite) :
    (∑' p, weightedRow G R w F p) = ∑ x ∈ R.roots, w x * ∑' y, F x y := by
  have hs : Summable (weightedRow G R w F) := summable_of_hasFiniteSupport (weightedRow_finite G R w F hF)
  rw [hs.tsum_prod]
  simp only [weightedRow,tsum_mul_left,tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => w x * ∑' y, F x y)

lemma massTransport (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (hw : ∀ (φ : G.Aut) x, w (φ.vertex x) = w x)
    (hbal : ∀ x y, w x * (G.suborbitCard x y : ℝ) = w y * (G.suborbitCard y x : ℝ))
    (F : V → V → ℝ) (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (hrow : ∀ x, (Function.support (F x)).Finite)
    (hcol : ∀ y, (Function.support (fun x => F x y)).Finite) :
    (∑ x ∈ R.roots, w x * ∑' y, F x y) = ∑ y ∈ R.roots, w y * ∑' x, F x y := by
  let F' := fun x y => F y x
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := hF φ y x
  have hs : Summable (weightedRow G R w F) := summable_of_hasFiniteSupport (weightedRow_finite G R w F hrow)
  have ht : Summable (weightedRow G R w F') := summable_of_hasFiniteSupport (weightedRow_finite G R w F' hcol)
  rw [←tsum_weightedRow G R w F hrow,←tsum_weightedRow G R w F' hcol]
  calc
    _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q}, weightedRow G R w F p :=
      (hs.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq.symm
    _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          weightedRow G R w F' p := by
      apply tsum_congr
      intro q
      induction q using Quotient.inductionOn' with
      | h p =>
        change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2}, weightedRow G R w F z) =
          ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1}, weightedRow G R w F' z
        rw [fiber_sum G R hc hl w hw F hF,fiber_sum G R hc hl w hw F' hF',hbal]
    _ = ∑' p, weightedRow G R w F' p := by
      exact (G.swapPairOrbit.tsum_eq (fun q =>
        ∑' p : (pairMap G R) ⁻¹' {q}, weightedRow G R w F' p)).trans
          (ht.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedTransportENNReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

def ennRow (F : V → V → ℝ≥0∞) (p : R.RootedPair) : ℝ≥0∞ := F p.1 p.2

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_NormalizedIncidenceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def normalizedSelectedIncidence (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  (∑' e, if e∈G.incidentEdges (G.cluster ω x) then H ω e*G.bondWeight x e else 0)*
    G.reciprocalClusterMass ω x

def normalizedIncidenceTransport (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  ∑' e, if e∈G.incidentEdges (G.cluster ω x) ∧ y∈G.ends e then
    H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ExpectedIncidenceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def selectedIncidenceReturn (hl : G.LocallyFinite) (H : Set E → E → ℝ≥0∞)
    (ω : Set E) (y : V) : ℝ≥0∞ :=
  ∑ e∈(hl y).toFinset, H ω e*G.incidentClusterCount ω e

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyPeaks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def heavyPeakTransport (N : ℕ) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if G.modularMass x (G.cluster ω x) = ∞ ∧ G.peakBound N ω x ∧ y∈G.clusterPeaks ω x then 1 else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def peakReturn (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.clusterPeak ω x then ((G.clusterPeaks ω x).encard : ℝ≥0∞)⁻¹ else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedPeakTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def normalizedClusterVolume (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.clusterPeakRatio ω x=0 then 0 else (G.clusterPeakRatio ω x)⁻¹

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakVolumeBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def peakVolumeBand (T U : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U then
    G.peakReturn ω x else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def centeredCoefficient (p : ℝ) (ω : Set E) (e : E) : ℝ := if e∈ω then 1-p else -p

def weightedIncidenceTerm (p : ℝ) (ω : Set E) (x : V) (e : E) : ℝ :=
  if e∈G.incidentEdges (G.cluster ω x) then
    (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0

def weightedDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  ∑' e, G.weightedIncidenceTerm p ω x e

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_NormalizedDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def normalizedAbsoluteDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ENNReal.ofReal |G.weightedDiscrepancy p ω x| / G.modularMass x (G.cluster ω x)

def discrepancyVolumeBand (p : ℝ) (T U : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U then
    G.normalizedAbsoluteDiscrepancy p ω x else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_LevelContactGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def exteriorCluster (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set V :=
  G.cluster (ω∩G.inducedEdges {v | j ≤ π v}) o

def levelContacts (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set V :=
  G.exteriorCluster π j o ω∩{v | π v=j}

def contactDrop (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set E :=
  {e | ∃ v∈G.levelContacts π j o ω, ∃ w, π w<j ∧ G.ends e=s(v,w)}

def minimumLevel (π : V → ℤ) (o : V) (j : ℤ) : Set (Set E) :=
  G.hitEvent o {v | π v=j}\G.hitEvent o {v | π v<j}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_LevelContactMeasurability
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

namespace BernoulliProduct
variable {E : Type*}
lemma measurable_inter_block (X : Set E) :
    @Measurable (Set E) (Set E) (blockSigma X) inferInstance (fun ω => ω∩X) := by
  have hh := measurable_forceOn_block Xᶜ (∅ : Set E)
  rw [compl_compl] at hh
  have he : forceOn Xᶜ (∅ : Set E)=(fun ω : Set E => ω∩X) := by
    unfold forceOn
    funext configuration
    apply Set.ext
    intro edge
    rw [Set.mem_inter_iff]
    simp only [Membership.mem, Set.Mem]
    split_ifs with hedge
    · exact ⟨False.elim, fun hmem => hedge hmem.2⟩
    · exact ⟨fun hmem => ⟨hmem, not_not.mp hedge⟩, And.left⟩
  rw [he] at hh
  exact hh
end BernoulliProduct

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

variable [Countable V] [Countable E]

def fewContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | ∃ U : Finset V, G.levelContacts π j o ω=(U : Set V) ∧ U.Nonempty ∧ U.card<k}

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedDiscrepancyLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def restrictedWeightedTerm (s : Set E) (p : ℝ) (ω : Set E) (x : V) (e : E) : ℝ :=
  if e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x) then
    (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0

def restrictedWeightedDiscrepancy (s : Set E) (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  ∑' e, G.restrictedWeightedTerm s p ω x e

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_DiscrepancyTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators Topology

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

def discrepancyVolumeTail (p : ℝ) (T : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x then G.normalizedAbsoluteDiscrepancy p ω x else 0

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_MonotoneBernoulli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct

variable {E : Type*}

def markLaw : Measure (E → ℝ) := Measure.infinitePi (fun _ : E => Priority.uniform01)

instance instIsProbabilityMeasureForallRealMarkLaw : IsProbabilityMeasure (markLaw (E := E)) := by
  unfold markLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def atParameter (p : unitInterval) (u : E → ℝ) : Set E := {e | u e < p}

def reindexMarks (e : E ≃ E) (u : E → ℝ) : E → ℝ := fun x => u (e.symm x)

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def heavyFlag (p : unitInterval) (u : E → ℝ) (x : V) : Prop :=
  G.modularMass x (G.cluster (atParameter p u) x) = ∞

def heavyRestrictedPeakTransport (p q : unitInterval) (u : E → ℝ) (x y : V) : ℝ≥0∞ :=
  if G.heavyFlag p u x then G.peakRatioTransport (atParameter q u) x y else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_SignedDiscrepancyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def normalizedSignedDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  G.weightedDiscrepancy p ω x / (G.modularMass x (G.cluster ω x)).toReal

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_CriticalHeavyIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterCountDrop (ω : Set E) (e : E) : ℝ :=
  (G.incidentClusterCount (ω\{e}) e).toReal -
    (G.incidentClusterCount (insert e ω) e).toReal

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ForcedDisconnectContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def forcedClosedSeparated (ω : Set E) (e : E) : Prop :=
  ∃ a∈G.ends e, ∃ b∈G.ends e, ¬(G.openGraph (ω\{e})).Reachable a b

def disconnectedIndicator (ω : Set E) (e : E) : ℝ :=
  if G.forcedClosedSeparated ω e then 1 else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyFiniteGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def distinctHeavyEvent (o x y : V) : Set (Set E) :=
  {ω | G.modularMass o (G.cluster ω x)=∞ ∧ G.modularMass o (G.cluster ω y)=∞ ∧
    ¬(G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ContractingDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def safeBallDomain (o : V) (T : ℝ) (R : ℕ) : Set V :=
  {x | ∃ z, x∈G.vertexBall z R ∧
    ∀ y∈G.vertexBall z R, G.modularRatio y o≤T}

def InsideWalk (S : Set V) (x y : V) (n : ℕ) : Prop :=
  ∃ p : G.fullGraph.Walk x y, p.length≤n ∧ ∀ v∈p.support, v∈S

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SelectedFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

def selectedEvent (d : Set E → I) (A : I → Set (Set E)) : Set (Set E) :=
  {ω | ω∈A (d ω)}

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SliceExploration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal symmDiff Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def freshClusterBoundary (X : Set E) (v : V) (ω : Set E) : Set E :=
  G.cutEdges (G.cluster (ω∩X) v) \ X

def smallFreshBoundary (X : Set E) (v : V) (M : ℕ) : Set (Set E) :=
  {ω | (G.cluster (ω∩X) v).Finite ∧ (G.freshClusterBoundary X v ω).ncard ≤ M}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_OpenFrontierDivergence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def fewOpenFreshBoundary (X : Set E) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | (G.cluster (ω∩X) v).Finite ∧ (G.freshClusterBoundary X v ω ∩ ω).ncard ≤ N}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_RestrictedSeed
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def restrictedSeed (A T : Set V) (S : Set E) : Set (Set E) :=
  {ω | ω∩S∈G.seedHitEvent A T}

lemma measurableSet_restrictedSeed [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet[blockSigma S] (G.restrictedSeed A T S) :=
  (G.measurableSet_seedHitEvent A T).preimage (measurable_inter_block S)

lemma restrictedSeed_measurable [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet (G.restrictedSeed A T S) :=
  (blockSigma_le S) _ (G.measurableSet_restrictedSeed A T S)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph

variable {V : Type*}

def sign (b : Bool) : ℝ := if b then 1 else -1

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_MoveWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def boxMove (t z : V → ℝ) (m : ℕ) (precision radius : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.vertexBall y m, ∃ b, ∃ w : (G.openGraph ω).Walk a b,
    (∀ x∈w.support, |t x-t y| ≤ radius ∧ |z x-z y| ≤ radius) ∧
    |t b-(t y+1)|≤precision ∧ |z b-(z y+s)|≤precision}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_MoveExit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def axisExit (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) : Set (Set E) :=
  G.restrictedSeed A {x | L≤Corridor.sign b*u x ∧ Corridor.sign b*u x≤L+D ∧
    |u x|≤L+D ∧ |v x|≤W} (G.inducedEdges {x | |u x|≤L+D ∧ |v x|≤W})

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_StripMoves
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stripPercolates (v : V → ℝ) (W : ℝ) : Set (Set E) :=
  {ω | ω∩G.inducedEdges {x | |v x|≤W}∈G.percolates}

def someStripPercolates (v : V → ℝ) : Set (Set E) :=
  ⋃ n : ℕ, G.stripPercolates v n

def seedStripInfinite (v : V → ℝ) (A : Set V) (W : ℝ) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a).Infinite}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_FreshExitWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def freshExitEvent (S : Set V) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | ∃ F : Finset E, N≤F.card ∧
    (F : Set E)⊆G.freshClusterBoundary (G.inducedEdges S) v ω∩ω}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_DomainFreshExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def domainFreshExitEvent (D S : Set V) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | ω∩G.inducedEdges D ∈ G.freshExitEvent S v N}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_LightSliceFrontier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def modularUpperSlice (o : V) (ε : ℝ) : Set V := {x | ε ≤ G.modularRatio x o}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_NestedLayerBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def boundedDomainFreshExitEvent (D S : Set V) (v : V) (N : ℕ) (M : ℝ≥0∞) : Set (Set E) :=
  G.domainFreshExitEvent D S v N ∩
    {ω | G.modularMass v (G.cluster ((ω∩G.inducedEdges D)∩G.inducedEdges S) v)≤M}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_OpenRay
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure OpenRay (ω : Set E) where
  vertex : ℕ → V
  injective : Function.Injective vertex
  adjacent : ∀ n, (G.openGraph ω).Adj (vertex n) (vertex (n+1))

@[ext]
structure RayPrefix (ω : Set E) (o : V) (n : ℕ) where
  vertex : Fin (n+1) → V
  start : vertex 0=o
  adjacent : ∀ i : Fin n, (G.openGraph ω).Adj (vertex i.castSucc) (vertex i.succ)
  injective : Function.Injective vertex
  ball : ∀ i, vertex i∈G.vertexBall o i.val

def RayPrefix.restrict {ω : Set E} {o : V} {i j : ℕ} (h : i≤j)
    (p : G.RayPrefix ω o j) : G.RayPrefix ω o i where
  vertex k := p.vertex (Fin.castLE (Nat.succ_le_succ h) k)
  start := p.start
  adjacent k := p.adjacent (Fin.castLE h k)
  injective := by
    intro x y heq
    exact Fin.ext (congrArg (fun z : Fin (j+1) => z.val) (p.injective heq))
  ball k := p.ball (Fin.castLE (Nat.succ_le_succ h) k)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteSusceptibility
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation
open FiniteProduct

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def openIncident (ω : Set E) (v : V) : Set E :=
  G.incidentEdges (G.cluster ω v) ∩ ω

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_LayerExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def entrySeeds (D : Set V) (o : V) (ω : Set E) : Set V :=
  G.cluster (ω∩(G.inducedEdges D)ᶜ) o ∩ D

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_LayerCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def layerComponent (D H : Set V) (ω : Set E) (x : V) : Set V :=
  G.cluster ((ω∩G.inducedEdges D)∩G.inducedEdges Hᶜ) x

def openLayerExits (D H : Set V) (ω : Set E) (x : V) : Set E :=
  G.freshClusterBoundary (G.inducedEdges Hᶜ) x (ω∩G.inducedEdges D)∩(ω∩G.inducedEdges D)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_LayerExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def seedExpectation (q : unitInterval) (D : Set V) (o : V) : ℝ≥0∞ :=
  ∑' x, G.law q {ω | x∈G.entrySeeds D o ω}

def goodEntrySeeds (D H : Set V) (o : V) (N M : ℕ) (ω : Set E) : Set V :=
  G.entrySeeds D o ω ∩ {x | x∉H ∧ ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M}

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedGhost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

def ghostKernel (h x : ℝ) : ℝ := 1 - Real.exp (-h * x)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ)

def ghostMagnetization (h : ℝ) : ℝ := ∫ ω, ghostKernel h (X ω) ∂μ

def ghostMagnetizationDerivative (h : ℝ) : ℝ :=
  ∫ ω, X ω * Real.exp (-h * X ω) ∂μ

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

def connectionMeasure (p : unitInterval) (x y : V) : ℝ≥0∞ :=
  G.law p {ω | (G.openGraph ω).Reachable x y}

def tiltedSusceptibility (p : unitInterval) (a : ℝ) (x : V) : ℝ≥0∞ :=
  ∑' y, G.connectionMeasure p x y * G.stabilizerWeight x y ^ a

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedGhostSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

def quarterTiltedMass (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if (G.openGraph ω).Reachable x y then G.stabilizerWeight x y ^ (1 / 4 : ℝ) else 0

def quarterGhostMagnetization (p : unitInterval) (x : V) (h : ℝ) : ℝ :=
  Percolation.BenjaminiSchramm.ghostMagnetization (G.law p)
    (fun ω => (G.quarterTiltedMass ω x).toReal) h

def quarterGhostDerivative (p : unitInterval) (x : V) (h : ℝ) : ℝ :=
  Percolation.BenjaminiSchramm.ghostMagnetizationDerivative (G.law p)
    (fun ω => (G.quarterTiltedMass ω x).toReal) h

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ModularSlabs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def modularLogHeight (x y : V) : ℝ := Real.log (G.modularRatio y x)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitHeightComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitAdjustedHeight (a : V → ℝ) (x y : V) : ℝ :=
  G.modularLogHeight x y + Real.log (a y) - Real.log (a x)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitNeighborChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

abbrev VertexOrbit := MulAction.orbitRel.Quotient G.Aut V

def vertexOrbit (x : V) : G.VertexOrbit := Quotient.mk'' x

@[simp] lemma vertexOrbit_aut (φ : G.Aut) (x : V) :
    G.vertexOrbit (φ.vertex x) = G.vertexOrbit x :=
  Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨φ,rfl⟩)

def modularWalkDegree (x : V) : ℕ := (G.fullGraph.neighborSet x).ncard

def orbitNeighborCount (hl : G.LocallyFinite) (i j : G.VertexOrbit) : ℕ :=
  (((G.finite_neighbors hl i.out).toFinset).filter fun y => G.vertexOrbit y = j).card

def orbitWalkKernel (hl : G.LocallyFinite) (i j : G.VertexOrbit) : ℝ :=
  G.orbitNeighborCount hl i j / (G.modularWalkDegree i.out : ℝ)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stationaryOrbitWeight (μ : G.VertexOrbit → ℝ) (x : V) : ℝ :=
  μ (G.vertexOrbit x) / G.modularWalkDegree x

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

def orbitEquiv : {x // x ∈ R.roots} ≃ G.VertexOrbit :=
  Equiv.ofBijective (fun x => G.vertexOrbit x) (by
    constructor
    · intro x y h
      obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
      exact Subtype.ext (R.unique x x.property y y.property φ hφ)
    · intro q
      obtain ⟨x,hx,φ,hφ⟩ := R.cover q.out
      refine ⟨⟨x,hx⟩,?_⟩
      have h := G.vertexOrbit_aut φ x
      rw [hφ] at h
      simpa only [vertexOrbit,Quotient.out_eq'] using h.symm)

end OrbitRepresentatives

def orbitNeighborTransport (a : V → ℝ) (i : G.VertexOrbit) (x y : V) : ℝ :=
  if G.vertexOrbit y = i ∧ G.fullGraph.Adj x y then a x else 0

def weightedNeighborIncoming (a : V → ℝ) (y : V) : ℝ :=
  ∑' x, if G.fullGraph.Adj x y then a x * G.modularRatio x y else 0

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SusceptibilityDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realSusceptibility (G : BondGraph V E) (x : V) (t : ℝ) : ℝ :=
  ∑' y, realTwoPoint G x y t

@[simp] theorem realSusceptibility_coe (G : BondGraph V E) (x : V) (p : unitInterval) :
    realSusceptibility G x (p : ℝ) = susceptibility G p x := by
  simp only [realSusceptibility,realTwoPoint_coe,susceptibility]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EncounterGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def separatedInfiniteTupleEvent {k : ℕ} (v : Fin k → V) : Set (Set E) :=
  {ω | (∀ i, (G.cluster ω (v i)).Infinite) ∧
    Pairwise (fun i j => ¬(G.openGraph ω).Reachable (v i) (v j))}

def encounterEvent (J : Set E) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | ∃ v : Fin k → V, (∀ i, (G.openGraph ω).Reachable o (v i)) ∧
    (∀ i, (G.cluster (ω\J) (v i)).Infinite) ∧
    Pairwise (fun i j => ¬(G.openGraph (ω\J)).Reachable (v i) (v j))}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_InvariantFiniteSets
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def vertexSetBound (_G : BondGraph V E) (A : Set E → Set V) (N : ℕ) (ω : Set E) : Prop :=
  ∃ S : Finset V, S.card≤N ∧ A ω ⊆ S

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_LightClusterNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def lightInfinitePeaks (ω : Set E) : Set V :=
  {v | ω∈G.lightInfiniteEvent v v ∧ G.clusterPeak ω v}

def lightClusterCover (ω : Set E) (S : Set V) : Prop :=
  ∀ v, ω∈G.lightInfiniteEvent v v → ∃ s∈S, (G.openGraph ω).Reachable v s

def infinitelyManyLightClusters (ω : Set E) : Prop :=
  ∀ S : Finset V, ∃ v, ω∈G.lightInfiniteEvent v v ∧
    ∀ s∈S, ¬(G.openGraph ω).Reachable v s

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_LightTwoPointDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def upperEscapeEvent (v : V) (R : ℕ) : Set (Set E) :=
  {ω | ∃ x, x∈G.clusterUpperSet ω v ∧ x∉G.vertexBall v R}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_BallCutGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ballCut (o : V) (n : ℕ) : Set E := G.cutEdges (G.vertexBall o n)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BandScale
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterBand (o : V) (s : ℕ) : Set (Set E) :=
  G.clusterTail o s \ G.clusterTail o (s ^ 2)

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_DeletedTailGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation
namespace BondGraph
open ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

def exitEndpoint (U : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ U then (G.ends e).out.2 else (G.ends e).out.1

def exitVertices (U : Set V) : Finset V :=
  (G.incidentEdges U).toFinset.image (G.exitEndpoint U)

def smallDamage (H : SimpleGraph V) (U : Set V) (s : ℕ) : Finset V :=
  U.toFinset ∪ ((G.exitVertices U).filter
    (fun w => (component (delete H U) w).toFinset.card < s)).biUnion
      (fun w => (component (delete H U) w).toFinset)

def tailCount (H : SimpleGraph V) (B : Finset V) (s : ℕ) : ℝ :=
  ∑ v∈B, if s≤(component H v).toFinset.card then 1 else 0

def exteriorTailCount (H : SimpleGraph V) (U : Set V) (B : Finset V) (s : ℕ) : ℝ :=
  ∑ v∈B, if v∉U ∧ s≤(component (delete H U) v).toFinset.card then 1 else 0

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_Unimodularity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure UnimodularRoot where
  roots : Finset V
  weight : V → ℝ
  positive : ∀ u ∈ roots, 0 < weight u
  normalized : ∑ u ∈ roots, weight u = 1
  cover : ∀ v : V, ∃ u ∈ roots, ∃ φ : G.Aut, φ.vertex u = v
  balance : ∀ F : V → V → ℝ,
    (∀ (φ : G.Aut) u v, F (φ.vertex u) (φ.vertex v) = F u v) →
    (∀ u, (Function.support (F u)).Finite) →
    (∀ v, (Function.support (fun u => F u v)).Finite) →
    (∑ u ∈ roots, weight u * ∑' v, F u v) =
      ∑ v ∈ roots, weight v * ∑' u, F u v

def bondShare (e : E) : ℝ := 1 / (G.ends e).toFinset.card

def splitBondTransport (F : V → E → ℝ) (u v : V) : ℝ :=
  ∑' e, if v ∈ G.ends e then G.bondShare e * F u e else 0

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_UnimodularGeometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def CombinatoriallyUnimodular.unimodularRoot (hu : G.CombinatoriallyUnimodular)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) : G.UnimodularRoot := by
  let R := G.orbitRepresentatives hq
  let Z := ∑ x ∈ R.roots, G.modularRatio o x
  have hZ : 0 < Z := by
    obtain ⟨u,hu,_,_⟩ := R.cover o
    exact Finset.sum_pos' (fun x _ => (G.modularRatio_pos hc hl o x).le)
      ⟨u,hu,G.modularRatio_pos hc hl o u⟩
  let w := fun x => G.modularRatio o x / Z
  have hw (φ : G.Aut) (x : V) : w (φ.vertex x) = w x := by
    simp only [w,CombinatoriallyUnimodular.rootWeight_invariant G hu hc hl]
  have hbal (x y : V) : w x * (G.suborbitCard x y : ℝ) = w y * (G.suborbitCard y x : ℝ) := by
    simp only [w,div_mul_eq_mul_div]
    rw [G.modularRatio_card_balance hc hl]
  refine ⟨R.roots,w,?_,?_,R.cover,?_⟩
  · intro x _
    exact div_pos (G.modularRatio_pos hc hl o x) hZ
  · change (∑ x ∈ R.roots, G.modularRatio o x / Z) = 1
    rw [←Finset.sum_div,div_self (ne_of_gt hZ)]
  · exact OrbitRepresentatives.massTransport G R hc hl w hw hbal

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_MainResidualBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def twoHeavyDistinctEvent (o x y : V) : Set (Set E) :=
  G.heavyClusterEvent o x ∩ G.heavyClusterEvent o y ∩
    {ω | ¬ (G.openGraph ω).Reachable x y}

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_HeightCuts
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def heightCut (π : V → ℤ) (t : ℤ) : Set E := G.cutEdges {v | t < π v}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphActionCoordinates
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]

def PreservesEnds : Prop :=
  ∀ (g : Λ) (e : E), G.ends (g • e)=Sym2.map (fun v : V => g • v) (G.ends e)

def smulAut (h : G.PreservesEnds (Λ := Λ)) (g : Λ) : G.Aut where
  vertex := MulAction.toPerm g
  edge := MulAction.toPerm g
  preserves := h g

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ComponentCritical
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma image_restrict (S : Set V) (ω : Set E) :
    Subtype.val '' (Subtype.val ⁻¹' ω : Set (G.inducedEdges S))=ω∩G.inducedEdges S := by
  ext e
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,a.property⟩
  · rintro ⟨he,hs⟩
    exact ⟨⟨e,hs⟩,he,rfl⟩

def domainComponent (S : Set V) (o : V) : Set V := G.cluster (G.inducedEdges S) o

def OpenRay.induce {ω : Set E} (r : G.OpenRay ω) (S : Set V)
    (hS : ∀ n, r.vertex n∈S) :
    (G.induce S).OpenRay (Subtype.val ⁻¹' ω) where
  vertex n := ⟨r.vertex n,hS n⟩
  injective := fun _ _ h => r.injective (congrArg Subtype.val h)
  adjacent n := by
    apply (G.induce_adj S (Subtype.val ⁻¹' ω) _ _).mpr
    rw [G.image_restrict]
    exact (G.open_induced_adj S ω _ _).mpr ⟨r.adjacent n,hS n,hS (n+1)⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_InducedAutomorphism
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.inducedEdges_mem (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (e : E) :
    phi.edge e∈G.inducedEdges S ↔ e∈G.inducedEdges S := by
  constructor
  · intro h x hx
    apply (hS x).mp
    apply h (phi.vertex x)
    rw [phi.preserves]
    exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩
  · intro h y hy
    rw [phi.preserves] at hy
    obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hy
    exact (hS x).mpr (h x hx)

def Aut.restrict (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) : (G.induce S).Aut where
  vertex :=
    { toFun := fun x => ⟨phi.vertex x,(hS x).mpr x.property⟩
      invFun := fun x => ⟨phi.vertex.symm x,(hS (phi.vertex.symm x)).mp
        (by simpa only [Equiv.apply_symm_apply] using x.property)⟩
      left_inv := fun x => Subtype.ext (phi.vertex.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (phi.vertex.apply_symm_apply x) }
  edge :=
    { toFun := fun e => ⟨phi.edge e,(Aut.inducedEdges_mem G phi S hS e).mpr e.property⟩
      invFun := fun e => ⟨phi.edge.symm e,(Aut.inducedEdges_mem G phi S hS (phi.edge.symm e)).mp
        (by simpa only [Equiv.apply_symm_apply] using e.property)⟩
      left_inv := fun e => Subtype.ext (phi.edge.symm_apply_apply e)
      right_inv := fun e => Subtype.ext (phi.edge.apply_symm_apply e) }
  preserves e := by
    apply Sym2.map.injective Subtype.val_injective
    rw [G.induce_ends_map,Sym2.map_map]
    change G.ends (phi.edge e.val)=Sym2.map (fun x : S => phi.vertex x.val) ((G.induce S).ends e)
    calc
      G.ends (phi.edge e.val)=Sym2.map phi.vertex (G.ends e.val) := phi.preserves e.val
      _=Sym2.map phi.vertex (Sym2.map (Subtype.val : S → V) ((G.induce S).ends e)) :=
        congrArg (Sym2.map phi.vertex) (G.induce_ends_map S e).symm
      _=_ := Sym2.map_map _

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_RestrictedAction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} (G : BondGraph V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]

def domainPreserver (C : Set V) : Subgroup Λ where
  carrier := {g | ∀ x, g • x∈C ↔ x∈C}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg x
    simpa only [smul_inv_smul] using (hg (g⁻¹ • x)).symm

@[instance_reducible] def restrictedVertexAction (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    MulAction L C where
  smul g x := ⟨(g : Λ) • x.val,(hL g.property x.val).mpr x.property⟩
  one_smul x := Subtype.ext (one_smul Λ x.val)
  mul_smul g h x := Subtype.ext (mul_smul (g : Λ) (h : Λ) x.val)

@[instance_reducible] def restrictedEdgeAction (ha : G.PreservesEnds (Λ := Λ))
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    MulAction L (G.inducedEdges C) where
  smul g e := ⟨(g : Λ) • e.val,
    (Aut.inducedEdges_mem G (G.smulAut ha g.val) C (hL g.property) e.val).mpr e.property⟩
  one_smul e := Subtype.ext (one_smul Λ e.val)
  mul_smul g h e := Subtype.ext (mul_smul (g : Λ) (h : Λ) e.val)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_ComponentAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ T : Type*} (G : BondGraph V E)
  [Group Λ] [Group T] [MulAction Λ V] [MulAction Λ E]

def componentKernel (a : Λ →* T) (C : Set V) : Subgroup Λ :=
  a.ker ⊓ domainPreserver C

lemma componentKernel_le (a : Λ →* T) (C : Set V) :
    componentKernel a C≤domainPreserver C := inf_le_right

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ActionOrbitTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace ActionOrbitTransport
variable (Λ X : Type*) [Group Λ] [MulAction Λ X]

abbrev PairOrbit := MulAction.orbitRel.Quotient Λ (X × X)
def pairOrbit (x y : X) : PairOrbit Λ X := Quotient.mk'' (x,y)
def stabilizerOrbit (x y : X) : Set X := MulAction.orbit (MulAction.stabilizer Λ x) y
def suborbitCard (x y : X) : ℕ := (stabilizerOrbit Λ X x y).ncard

lemma mem_stabilizerOrbit {x y z : X} : z ∈ stabilizerOrbit Λ X x y ↔
    ∃ φ : Λ, φ • x = x ∧ φ • y = z := by
  simp only [stabilizerOrbit,MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨φ,hφ⟩
    exact ⟨φ,φ.property,hφ⟩
  · rintro ⟨φ,hx,hy⟩
    exact ⟨⟨φ,hx⟩,hy⟩

lemma pairOrbit_eq {x y u v : X} : pairOrbit Λ X x y = pairOrbit Λ X u v ↔
    ∃ φ : Λ, φ • x = u ∧ φ • y = v := by
  constructor
  · intro h
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
    exact ⟨φ,congrArg Prod.fst hφ,congrArg Prod.snd hφ⟩
  · rintro ⟨φ,hx,hy⟩
    apply Eq.symm
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext hx hy⟩

lemma smul_pairOrbit (φ : Λ) (x y : X) :
    pairOrbit Λ X (φ • x) (φ • y) = pairOrbit Λ X x y :=
  (pairOrbit_eq Λ X |>.mpr ⟨φ,rfl,rfl⟩).symm

end ActionOrbitTransport
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularLevelGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[instance_reducible] def autEdgeAction : MulAction G.Aut E where
  smul φ e := φ.edge e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance instMulActionAut_1 : MulAction G.Aut E := G.autEdgeAction

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteIndexAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ Q : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

def quotientSubgroupMap (ρ : Λ →* Q) (N : Subgroup Q) : N.comap ρ →* N where
  toFun g := ⟨ρ g.val,g.property⟩
  map_one' := Subtype.ext (ρ.map_one)
  map_mul' g h := Subtype.ext (ρ.map_mul g.val h.val)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_AlgebraicDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

universe u

inductive AlgebraicDescent : (N : Type u) → [Group N] → Prop
  | finite (N : Type u) [Group N] [Finite N] : AlgebraicDescent N
  | cyclic (N : Type u) [Group N]
      (φ : N →* Multiplicative ℤ) (hφ : Surjective φ)
      (hf : (φ.ker : Set N).Finite) : AlgebraicDescent N
  | plane (N : Type u) [Group N]
      (φ : N →* Multiplicative (ℤ×ℤ)) (hφ : Surjective φ)
      (lower : ∀ J : Subgroup N, J≤φ.ker → AlgebraicDescent J) : AlgebraicDescent N

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripCompactness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def seedDomainTail (A S : Set V) (n : ℕ) : Set (Set E) :=
  ⋃ a∈A, (fun ω : Set E => ω∩G.inducedEdges S) ⁻¹' G.clusterTail a n

def seedDomainInfinite (A S : Set V) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster (ω∩G.inducedEdges S) a).Infinite}

def prefix_inside_domain {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n)
    (S : Set V) (hS : ∀ i, p.vertex i∈S) :
    G.RayPrefix (ω∩G.inducedEdges S) a n := {
  vertex := p.vertex, start := p.start, injective := p.injective, ball := p.ball
  adjacent := fun i => (G.open_induced_adj S ω _ _).mpr
    ⟨p.adjacent i,hS i.castSucc,hS i.succ⟩ }

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_MovingStrips
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def parallelCoordinate (u v : V → ℝ) (a b : ℝ) (x : V) : ℝ := a*u x+b*v x
def normalCoordinate (u v : V → ℝ) (a b : ℝ) (x : V) : ℝ := -b*u x+a*v x

def longStripExit (u v : V → ℝ) (A : Set V) (W L a b : ℝ) : Set (Set E) :=
  G.restrictedSeed A
    ({x | |normalCoordinate u v a b x|≤W}∩{x | L≤|parallelCoordinate u v a b x|})
    (G.inducedEdges {x | |normalCoordinate u v a b x|≤W})

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_AdaptiveReveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct

structure RevealPartition (E I : Type*) [Fintype I] where
  block : I → Set E
  cell : I → Set (Set E)
  measurable : ∀ i, MeasurableSet[blockSigma (block i)] (cell i)
  disjoint : Pairwise (Disjoint on cell)
  cover : (⋃ i, cell i)=Set.univ

namespace RevealPartition
variable {E I : Type*} [Fintype I] (P : RevealPartition E I)

lemma exists_cell (σ : Set E) : ∃ i, σ∈P.cell i := by
  have h : σ∈⋃ i, P.cell i := by rw [P.cover]; trivial
  exact Set.mem_iUnion.mp h

lemma cell_unique {σ : Set E} {i j : I} (hi : σ∈P.cell i) (hj : σ∈P.cell j) : i=j := by
  by_contra h
  exact Set.disjoint_left.mp (P.disjoint h) hi hj

@[instance_reducible] def historySigma : MeasurableSpace (Set E) where
  MeasurableSet' A := ∀ i, MeasurableSet[blockSigma (P.block i)] (A∩P.cell i)
  measurableSet_empty := by intro i; simp
  measurableSet_compl := by
    intro A hA i
    have he : Aᶜ∩P.cell i=P.cell i\(A∩P.cell i) := by ext σ; simp; tauto
    rw [he]
    exact (P.measurable i).diff (hA i)
  measurableSet_iUnion := by
    intro A hA i
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (fun n => hA n i)

def probability (q : E → unitInterval) (A : Set (Set E)) (σ : Set E) : ℝ≥0∞ :=
  ∑ i, (P.cell i).indicator (blockProbability q (P.block i) A) σ

def enlarge (T : I → Set E) (hT : ∀ i, P.block i⊆T i) : RevealPartition E I where
  block := T
  cell := P.cell
  measurable i := (by
    have hmono : blockSigma (P.block i) ≤ blockSigma (T i) :=
      iSup₂_mono' (fun e he => ⟨e,hT i he,le_rfl⟩)
    exact hmono _ (P.measurable i))
  disjoint := P.disjoint
  cover := P.cover

def decide {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (d : I → Set E → J)
    (hd : ∀ i, @Measurable (Set E) J (blockSigma (P.block i)) inferInstance (d i)) :
    RevealPartition E (I×J) where
  block ij := P.block ij.1
  cell ij := P.cell ij.1∩(d ij.1 ⁻¹' {ij.2})
  measurable ij := (P.measurable ij.1).inter (hd ij.1 (MeasurableSet.singleton _))
  disjoint := by
    intro ij kl hne
    apply Set.disjoint_left.mpr
    intro σ hσ hτ
    have hi : ij.1=kl.1 := P.cell_unique hσ.1 hτ.1
    have hj : ij.2=kl.2 := by
      have ht : d kl.1 σ=kl.2 := hτ.2
      rw [← hi] at ht
      exact hσ.2.symm.trans ht
    exact hne (Prod.ext hi hj)
  cover := by
    apply Set.eq_univ_of_forall
    intro σ
    obtain ⟨i,hi⟩ := P.exists_cell σ
    exact Set.mem_iUnion.mpr ⟨(i,d i σ),hi,rfl⟩

end RevealPartition
end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_DecisionHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct

def DecisionCode : ℕ → Type
  | 0 => Unit
  | n+1 => DecisionCode n×Bool

instance instFintypeDecisionCode (n : ℕ) : Fintype (DecisionCode n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (DecisionCode n×Bool))

structure DecisionRule (E S : Type*) where
  initial : S
  block : S → Set E
  further : ℕ → S → Set E
  contained : ∀ n s, block s⊆further n s
  active : ℕ → S → Prop
  accept : ℕ → S → Set (Set E)
  measurable : ∀ n s, MeasurableSet[blockSigma (further n s)] (accept n s)
  update : ℕ → S → Bool → S
  block_update : ∀ n s b, block (update n s b)=further n s

namespace DecisionRule
variable {E S : Type*} (D : DecisionRule E S)

def state : (n : ℕ) → DecisionCode n → S
  | 0,_ => D.initial
  | n+1,(w,b) => D.update n (state n w) b

def partitionWithBlock : (n : ℕ) →
    {P : RevealPartition E (DecisionCode n) // ∀ w, P.block w=D.block (D.state n w)}
  | 0 => ⟨{
      block := fun _ => D.block D.initial
      cell := fun _ => Set.univ
      measurable := fun _ => MeasurableSet.univ
      disjoint := by intro i j hne; have he : i=j := @Subsingleton.elim Unit _ i j; exact (hne he).elim
      cover := Set.eq_univ_of_forall (fun _ => Set.mem_iUnion.mpr ⟨(),Set.mem_univ _⟩) },
      fun _ => rfl⟩
  | n+1 => by
      let P := (partitionWithBlock n).val
      have hP := (partitionWithBlock n).property
      let Q := P.enlarge (fun w => D.further n (D.state n w)) (by
        intro w
        rw [hP w]
        exact D.contained n (D.state n w))
      let T := Q.decide (fun w ω => if ω∈D.accept n (D.state n w) then true else false) (by
        intro w
        exact Measurable.ite (D.measurable n (D.state n w)) measurable_const measurable_const)
      refine ⟨T,?_⟩
      intro w
      change D.further n (D.state n w.1)=D.block (D.update n (D.state n w.1) w.2)
      exact (D.block_update n _ _).symm

def partition (n : ℕ) : RevealPartition E (DecisionCode n) :=
  (D.partitionWithBlock n).val

def failure (n : ℕ) : Set (Set E) := ⋃ w : DecisionCode n,
  (D.partition n).cell w∩{ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)}

def codeOf : (n : ℕ) → Set E → DecisionCode n
  | 0,_ => ()
  | n+1,ω => (codeOf n ω,if ω∈D.accept n (D.state n (codeOf n ω)) then true else false)

end DecisionRule
end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BalancedCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Boundary

def balancedPermutation {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) : Equiv.Perm E :=
  Equiv.ofFiberEquiv (fun v => Fintype.equivOfCardEq (hb v))

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SquareBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

abbrev Grid := ℤ×ℤ
abbrev Dir := Fin 4
abbrev Edge := Grid×Dir

def step : Dir → Grid := ![(1,0),(0,1),(-1,0),(0,-1)]
def leftOffset : Dir → Grid := ![(0,0),(-1,0),(-1,-1),(0,-1)]
def rightOffset : Dir → Grid := ![(0,-1),(0,0),(-1,0),(-1,-1)]
def tail (e : Edge) : Grid := e.1
def head (e : Edge) : Grid := e.1+step e.2
def leftSite (e : Edge) : Grid := e.1+leftOffset e.2
def rightSite (e : Edge) : Grid := e.1+rightOffset e.2

def squareBoundary (S : Set Grid) : Set Edge :=
  {e | leftSite e∈S ∧ rightSite e∉S}

def outgoingEquiv (S : Set Grid) (v : Grid) :
    {e : squareBoundary S // tail e=v} ≃ {d : Dir // (v,d)∈squareBoundary S} where
  toFun e := ⟨e.1.1.2,by
    have h := e.1.2
    have hv := e.2
    change e.1.1.1=v at hv
    change leftSite (e.1.1.1,e.1.1.2)∈S ∧ rightSite (e.1.1.1,e.1.1.2)∉S at h
    rwa [hv] at h⟩
  invFun d := ⟨⟨(v,d.1),d.2⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.2.symm rfl
  right_inv d := rfl

def incomingEquiv (S : Set Grid) (v : Grid) :
    {e : squareBoundary S // head e=v} ≃
      {d : Dir // (v-step d,d)∈squareBoundary S} where
  toFun e := ⟨e.1.1.2,by
    have hv : e.1.1.1=v-step e.1.1.2 := eq_sub_iff_add_eq.mpr e.2
    have h := e.1.2
    change leftSite (e.1.1.1,e.1.1.2)∈S ∧ rightSite (e.1.1.1,e.1.1.2)∉S at h
    rwa [hv] at h⟩
  invFun d := ⟨⟨(v-step d.1,d.1),d.2⟩,sub_add_cancel _ _⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    change (v-step e.1.1.2,e.1.1.2)=e.1.1
    exact Prod.ext (eq_sub_iff_add_eq.mpr e.2).symm rfl
  right_inv d := rfl

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ContourSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

def forwardDir (d : Dir) : Prop := d=1 ∨ d=2

def forwardIndices (e : ℕ → Edge) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => forwardDir (e i).2)

def outsideSites (e : ℕ → Edge) (n : ℕ) : Finset Grid :=
  (forwardIndices e n).image (fun i => rightSite (e i))

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ContourWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

def wordDir {n : ℕ} (w : Fin n → Dir) (i : ℕ) : Dir :=
  if h : i<n then w ⟨i,h⟩ else if h₀ : 0<n then w ⟨0,h₀⟩ else 0

def wordEdge {n : ℕ} (p : Grid) (w : Fin n → Dir) (i : ℕ) : Edge :=
  (p+∑ j∈Finset.range i, step (wordDir w j),wordDir w i)

def wordValid {n : ℕ} (p : Grid) (w : Fin n → Dir) : Prop :=
  wordEdge p w n=wordEdge p w 0 ∧ Set.InjOn (wordEdge p w) (Set.Iio n)

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ContourProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

namespace Boundary

def wordFailure {Ω : Type*} (B : Set Ω) (F : Grid → Set Ω)
    {n : ℕ} (w : Fin n → Dir) : Set Ω :=
  if wordValid (0,1) w then B∩⋂ z∈outsideSites (wordEdge (0,1) w) n, F z else ∅

end Boundary
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SlotContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.Boundary

def gridSlot (v : Grid) : ℕ := Nat.pair v.1.toNat v.2.toNat

def quadrant (v : Grid) : Prop := 0≤v.1 ∧ 0≤v.2

def gridFailure {Ω : Type*} (F : ℕ → Set Ω) (v : Grid) : Set Ω :=
  if quadrant v then F (gridSlot v) else ∅

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_PinnedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def predictionFailure (q : E → unitInterval) (F : Set E)
    (A C D : Set (Set E)) (δ : ℝ) : Set (Set E) :=
  Aᶜ ∪ (A∩{σ | (blockProbability q F C σ).toReal<1-δ}) ∪
    (A∩{σ | (blockProbability q F D σ).toReal<1-δ})

lemma measurableSet_predictionFailure (q : E → unitInterval) (F : Set E)
    (A C D : Set (Set E)) (hA : MeasurableSet[blockSigma F] A)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (δ : ℝ) :
    MeasurableSet[blockSigma F] (predictionFailure q F A C D δ) := by
  exact (hA.compl.union (hA.inter (measurableSet_lt
    (measurable_blockProbability q F C hC).ennreal_toReal measurable_const))).union
    (hA.inter (measurableSet_lt
      (measurable_blockProbability q F D hD).ennreal_toReal measurable_const))

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteSeedTree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ballRank (o v : V) : ℕ :=
  if h : ∃ n, v∈G.vertexBall o n then Nat.find h else 0

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ContactSelection
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

variable [Countable V] [Countable E]
def manyContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | (G.levelContacts π j o ω).Nonempty}\G.fewContacts π j o k

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SourceGraph
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def withSource (A : Set V) : BondGraph (Option V) (E⊕A) where
  ends e := match e with
    | Sum.inl b => Sym2.map Option.some (G.ends b)
    | Sum.inr a => s(none,some a.val)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_RelayScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def corridorRelay (t z : V → ℝ) (σ e ρ : ℝ) (L i : ℕ) : Set V :=
  if i=0 then relayMark t z 0 σ ρ
  else if i ≤ L then relayRegion t z σ e i else relayMark t z (L+1/2) σ ρ

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_RelayProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation
variable {Ω : Type*} [MeasurableSpace Ω]

namespace BernoulliProduct
variable {E : Type*}

def twoPredictions (q : E → unitInterval) (S : Set E) (C D : Set (Set E))
    (δ : ℝ) : Set (Set E) :=
  {σ | 1-δ ≤ (blockProbability q S C σ).toReal ∧
    1-δ ≤ (blockProbability q S D σ).toReal}

end BernoulliProduct
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseExit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ellipseExit (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) : Set (Set E) :=
  G.restrictedSeed A {x | ‖Psi x-(c : ℂ)‖≤2*zeta ∧ ‖Psi x‖≤1+zeta}
    (G.inducedEdges {x | ‖Psi x‖≤1+zeta})

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open LinearMap

namespace CriticalPercolation.EllipseLinear

def det (a b c d : ℝ) : ℝ := a*d-b*c

def time (a b c d x y : ℝ) : ℝ := ((d-b)*x+(a-c)*y)/det a b c d

def height (a b c d x y : ℝ) : ℝ := ((d+b)*x-(c+a)*y)/det a b c d

end CriticalPercolation.EllipseLinear
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_EllipseMoves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ellipseTime (Psi : V → ℂ) (c d : Circle) (x : V) : ℝ :=
  EllipseLinear.time (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im (Psi x).re (Psi x).im

def ellipseHeight (Psi : V → ℂ) (c d : Circle) (x : V) : ℝ :=
  EllipseLinear.height (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im (Psi x).re (Psi x).im

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseSeed
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def seedInfiniteEvent (A : Set V) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster ω a).Infinite}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stripTime (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (x : V) : ℝ :=
  Corridor.sign a*u x/U+Corridor.sign b*v x/Q

def stripHeight (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (x : V) : ℝ :=
  Corridor.sign a*u x/U-Corridor.sign b*v x/Q

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DirectionalTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def infiniteVertices (ω : Set E) : Set V := {v | (G.cluster ω v).Infinite}

def directionUnbounded (f : V → ℝ) : Set (Set E) :=
  {ω | ∀ n : ℕ, ∃ v, (n : ℝ)<f v ∧ v∈G.infiniteVertices ω}

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_StructuredCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E Λ N : Type*} (G : BondGraph V E)
  [Group Λ] [Group N] [MulAction Λ V] [MulAction Λ E]

def integerPairComplex (z : ℤ×ℤ) : ℂ := (z.1 : ℂ)+(z.2 : ℂ)*Complex.I

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitalPower
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def powerOn (O : Set V) (L : ℕ) : SimpleGraph O where
  Adj u v := u≠v ∧ v.val∈G.vertexBall u.val L
  symm := ⟨fun _ _ h => ⟨h.1.symm,G.vertexBall_comm.mp h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitPower (o : V) (L : ℕ) : SimpleGraph (MulAction.orbit G.Aut o) :=
  G.powerOn (MulAction.orbit G.Aut o) L

def orbitPowerHom (o : V) (L : ℕ) : G.Aut →*
    (G.orbitPower o L ≃g G.orbitPower o L) where
  toFun φ :=
    { toEquiv := MulAction.toPerm φ
      map_rel_iff' := by
        intro x y
        change (φ • x≠φ • y ∧ (φ • y).val∈G.vertexBall (φ • x).val L) ↔
          (x≠y ∧ y.val∈G.vertexBall x.val L)
        exact and_congr (MulAction.toPerm φ).injective.ne_iff
          (Aut.vertexBall_mem G φ x.val y.val L) }
  map_one' := by apply RelIso.ext; intro x; change (1 : G.Aut) • x=x; exact one_smul _ _
  map_mul' φ ψ := by
    apply RelIso.ext; intro x
    change (φ*ψ) • x=φ • (ψ • x)
    exact mul_smul _ _ _

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_OrbitalNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical Pointwise

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitBall (o : V) (r : ℕ) : Set V :=
  MulAction.orbit G.Aut o ∩ G.vertexBall o r

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_FaithfulOrbitalModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitalActionGroup (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    Subgroup (G.orbitPower o L ≃g G.orbitPower o L) :=
  ((G.orbitPowerHom o L).comp Λ.subtype).range

def orbitalActionMap (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    Λ →* G.orbitalActionGroup o L Λ :=
  ((G.orbitPowerHom o L).comp Λ.subtype).rangeRestrict

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FullOrbitalStructureTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def fullOrbitalQuotientHom (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal] :
    Λ →* (G.orbitPower o L ≃g G.orbitPower o L) ⧸ H :=
  (QuotientGroup.mk' H).comp ((G.orbitPowerHom o L).comp Λ.subtype)

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OrbitalStructureTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

instance orbitalActionGroup_action (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    MulAction (G.orbitalActionGroup o L Λ) (MulAction.orbit G.Aut o) where
  smul g u := g.val u
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def openFrontier (ω : Set E) (S : Set V) : Set V :=
  {z | z ∉ S ∧ ∃ u ∈ S, ∃ e ∈ ω, G e = s(u,z)}

def restrictedLayerCount (I : Set E) (A : Set V) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if y ∈ A ∧ Conn G (ω ∩ I) x y then 1 else 0

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_AvoidanceProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BernoulliProduct
variable {E ι : Type*} [Countable E]

def finiteBadUnion (F : Finset ι) (A : ι → Set (Set E)) : Set (Set E) :=
  {ω | ∃ i ∈ F, ω ∈ A i}

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NormalizedLayerTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def adjustedBandTransport (a : V → ℝ) (l u : ℝ) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y ∈ G.cluster ω x ∧ l ≤ G.orbitAdjustedHeight a x y ∧
    G.orbitAdjustedHeight a x y ≤ u then 1 else 0

def adjustedBandCount (a : V → ℝ) (l u : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.adjustedBandTransport a l u ω x y

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CeilingBandTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedCeilingBandTransport (a : V → ℝ) (c l u : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | G.orbitAdjustedHeight a x z ≤ c}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u then 1 else 0

def adjustedCeilingBandCount (a : V → ℝ) (c l u : ℝ)
    (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.adjustedCeilingBandTransport a c l u ω x y

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ConsistentLayers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def adjustedLayerIndex (a : V → ℝ) (R u : ℝ) (x y : V) : ℤ :=
  ⌊G.orbitAdjustedHeight a x y/R+u⌋-⌊u⌋

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FreshSlabConcatenation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def restrictedHit (I : Set E) (x : V) (A : Set V) : Set (Set E) :=
  {ω | ∃ y ∈ A, Conn G (ω ∩ I) x y}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedHit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

def weightHit (a : ℝ≥0∞) (x : V) : Set (Set E) :=
  {ω | ∃ y, (G.openGraph ω).Reachable x y ∧ a ≤ G.stabilizerWeight x y}

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NormalizedHalfspace
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedHalfspaceHit (a : V → ℝ) (x : V) (b t : ℝ) : Set (Set E) :=
  restrictedHit G.ends (Percolation.internalEdges G.ends {v | b ≤ G.orbitAdjustedHeight a x v}) x
    {v | t ≤ G.orbitAdjustedHeight a x v}

def infimalAdjustedCrossing (a : V → ℝ) (p : unitInterval) (t : ℝ) : ℝ≥0∞ :=
  ⨅ x, G.law p (G.adjustedHalfspaceHit a x 0 t)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CriticalHeightHit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedFullHit (a : V → ℝ) (x : V) (t : ℝ) : Set (Set E) :=
  {ω | ∃ y, t ≤ G.orbitAdjustedHeight a x y ∧ y ∈ G.cluster ω x}

def rootHeightHitProfile (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ :=
  ∑ x ∈ O.roots, (G.law p).real (G.adjustedFullHit a x (R*n))

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PairedSprinkling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def pairedParameters (q b : E → unitInterval) : E × Bool → unitInterval :=
  fun z => Percolation.pairParameter (q z.1) (b z.1) z.2

def whiteProjection (ω : Set (E × Bool)) : Set E :=
  (fun e => (e,true)) ⁻¹' ω

def blueProjection (ω : Set (E × Bool)) : Set E :=
  (fun e => (e,false)) ⁻¹' ω

def pairedUnion (ω : Set (E × Bool)) : Set E := {e | ∃ j, (e,j) ∈ ω}

def whiteBlock (Q : Set E) : Set (E × Bool) := {z | z.1 ∈ Q ∧ z.2=true}

def erasedWhiteParameters (q : E → unitInterval) (Q : Set E) : E → unitInterval :=
  fun e => if e ∈ Q then 0 else q e

def atParameters (q : E → unitInterval) (u : E → ℝ) : Set E := {e | u e < q e}

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ExteriorEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def exteriorEscape (S : Set V) (f : V → ℝ) (x u : V) : Set (Set E) :=
  {η | ∃ y, y ≠ x ∧ f x ≤ f y ∧ y ∉ S ∧ Conn G (η \ internalEdges G S) u y}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFirstMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedUpLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (n : ℕ) (x : V) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, restrictedLayerCount G.ends
    (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ (n : ℤ)})
    {v | G.adjustedLayerIndex a R u x v = (n : ℤ)} ω x ∂G.law p

def supAdjustedUpLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, ⨆ u, G.adjustedUpLayerMoment a R p n x u

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FractionalBandGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def fractionalReverseBandTransport (a : V → ℝ) (c l u δ : ℝ)
    (ω : Set E) (y x : V) : ℝ≥0∞ :=
  G.adjustedCeilingBandTransport a (c-u) (-u) (-l) ω y x *
    (G.adjustedCeilingBandCount a (c-u) (-u) (-l) ω y)^(-δ)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FractionalSlabGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedSlabBandTransport (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u then 1 else 0

def adjustedSlabBandCount (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.adjustedSlabBandTransport a d c l u ω x y

def fractionalReverseSlabTransport (a : V → ℝ) (d c l u δ : ℝ)
    (ω : Set E) (y x : V) : ℝ≥0∞ :=
  G.adjustedSlabBandTransport a (d-l) (c-u) (-u) (-l) ω y x *
    (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω y)^(-δ)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostCluster
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm

variable {V E : Type*} (G : BondGraph V E)

def quarterGhostWeight (x y : V) : ℝ≥0 :=
  (G.stabilizerWeight x y ^ (1 / 4 : ℝ)).toNNReal

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostMomentBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def quarterThreeQuarterMoment (p : unitInterval) (x : V) : ℝ≥0∞ :=
  ∫⁻ ω, G.quarterTiltedMass ω x ^ (3 / 4 : ℝ) ∂G.law p

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostTiltedTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

def ghostAvoid (h : ℝ) (m : ℝ≥0∞) : ℝ≥0∞ :=
  if m = ⊤ then 0 else ENNReal.ofReal (Real.exp (-h * m.toReal))

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm

variable {V E : Type*} (G : BondGraph V E)

def ghostHighTransport (h : ℝ) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if (G.openGraph ω).Reachable x y ∧ 1 < G.stabilizerWeight x y then
    ghostAvoid h (G.quarterTiltedMass ω x) * G.stabilizerWeight x y ^ (3 / 8 : ℝ)
  else 0

def ghostWeightedCount (h : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if (G.openGraph ω).Reachable x y then
    ghostAvoid h (G.quarterTiltedMass ω x) * G.stabilizerWeight x y ^ (3 / 8 : ℝ) else 0

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakHalfspaceGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedHalfspaceConn (a : V → ℝ) (b : ℝ) (ω : Set E) (base x y : V) : Prop :=
  Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
    {z | b ≤ G.orbitAdjustedHeight a base z}) x y

def adjustedStrictHalfspacePeak (a : V → ℝ) (b : ℝ) (ω : Set E) (base x : V) : Prop :=
  ∀ z, G.adjustedHalfspaceConn a b ω base x z → z ≠ x → G.orbitAdjustedHeight a x z < 0

def strictPeakBandTransport (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (y x : V) : ℝ≥0∞ :=
  if G.adjustedHalfspaceConn a (-r) ω y y x ∧
    G.adjustedStrictHalfspacePeak a (-r) ω y x ∧
      -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l then 1 else 0

def strictPeakSlabBandTransport (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if G.adjustedStrictHalfspacePeak a (l-r) ω x x ∧
    Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | u-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ 0}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u then 1 else 0

def strictPeakSlabBandCount (a : V → ℝ) (r l u : ℝ)
    (ω : Set E) (x : V) : ℝ≥0∞ := ∑' y, G.strictPeakSlabBandTransport a r l u ω x y

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakCorrelationAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def connectionAvoidingHit (I J : Set E) (u w : V) (T : Set V) : Set (Set E) :=
  {ω | Conn G (ω ∩ J) u w ∧ ω ∉ restrictedHit G I u T}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_MixedHeightMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def mixedHeightLayerMoment (a : V → ℝ) (p : unitInterval)
    (d c l u ad t : ℝ) (x : V) : ℝ≥0∞ :=
  ∑' y, if l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u then
    G.law p (connectionAvoidingHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a x z})
      (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
      x y {z | t ≤ G.orbitAdjustedHeight a x z}) else 0

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSurgeryProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def strictHeightPeakConnection (f : V → ℝ) (x z : V) : Set (Set E) :=
  {ω | Conn G ω x z ∧ ∀ y, Conn G ω z y → y ≠ z → f y < f z}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakOrbitComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def fullPeakDownHit (a : V → ℝ) (ell : ℝ) (x : V) : Set (Set E) :=
  strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a x) x x ∩
    restrictedHit G.ends Set.univ x {z | G.orbitAdjustedHeight a x z ≤ -ell}

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_WeightedPeakSlabComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def fullPeakDownProbability (O : G.OrbitRepresentatives) (a : V → ℝ)
    (p : unitInterval) (ell : ℝ) : ℝ≥0∞ :=
  ∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law p (G.fullPeakDownHit a ell x)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def frontierCount (I J : Set E) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' z, if z ∈ openFrontier G (ω ∩ J) (cluster G (ω ∩ I) x) then 1 else 0

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabFractionalProfileShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def lowerSlabFractionalProfile (a : V → ℝ) (p : unitInterval) (R L : ℝ) : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
      (∫⁻ ω, (G.adjustedSlabBandCount a (-k-r) 0 (-k-R) (-k+R) ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ζ*k+L*r))

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HalfspaceProfileBootstrap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def downwardHalfspaceFractionalProfile (a : V → ℝ) (p : unitInterval) (R q : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
    (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ 0})
      {v | -k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ζ*k))

def upwardHalfspaceFractionalProfile (a : V → ℝ) (p : unitInterval) (R q : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
    (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight a x v})
      {v | k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp ((-1+ζ)*k))

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerMaximumDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def adjustedFullLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (i : ℤ) (x : V) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R u x y=i} ω x ∂G.law p

def supAdjustedFullLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval) (i : ℤ) : ℝ≥0∞ :=
  ⨆ x, ⨆ u, G.adjustedFullLayerMoment a R p i x u

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakBandProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def strictPeakBandEvent (a : V → ℝ) (l u : ℝ) (x : V) : Set (Set E) :=
  {ω | ∃ z, l < G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u ∧
    ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a x) x z}

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakBandTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def peakUpBandTransport (a : V → ℝ) (l u : ℝ) (ω : Set E) (y x : V) : ℝ≥0∞ :=
  if l < G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ u ∧
    ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x then 1 else 0

def peakDownBandCount (a : V → ℝ) (l u : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.peakUpBandTransport a l u ω y x

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_UpwardFrontierProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def supAdjustedFrontierProbability (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, ⨆ u : ℝ, G.law p {ω | 0 < frontierCount G.ends
    (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v < (n : ℤ)}) Set.univ ω x}

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakConditionalLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def peakSurvivalProbability (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ∑ x ∈ O.roots, ENNReal.ofReal (a x)*
    G.law p {ω | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x}

def peakSurvivalLayerMoment (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (n l : ℕ) : ℝ≥0∞ :=
  ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
    {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
      (fun η => restrictedLayerCount G.ends Set.univ {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} η x) ω ∂G.law p)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakLayerCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def downwardLayerCost (a : V → ℝ) (R : ℝ) (g : ℕ → ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' l : ℕ, ENNReal.ofReal (g l)*restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R 0 x y= -(l : ℤ)} ω x

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSprinklingCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def peakDownClusterProperty (a : V → ℝ) (ell : ℝ) (x : V) (S : Set V) : Prop :=
  (∀ y ∈ S, y ≠ x → G.orbitAdjustedHeight a x y < 0) ∧
    ∃ y ∈ S, G.orbitAdjustedHeight a x y ≤ -ell

def exteriorAvoidance (S : Set V) (a : V → ℝ) (x : V) : Set (Set E) :=
  {η | ∀ u ∈ S, η ∉ exteriorEscape G.ends S (G.orbitAdjustedHeight a x) x u}

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_RootTiltedGhost
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E ι : Type*} (G : BondGraph V E)
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (root : ι → V)

def rootQuarterMass (z : ι × Set E) : ℝ≥0∞ := G.quarterTiltedMass z.2 (root z.1)

def rootQuarterGhostMagnetization (p : unitInterval) (h : ℝ) : ℝ :=
  Percolation.BenjaminiSchramm.ghostMagnetization (Measure.count.prod (G.law p))
    (fun z => (G.rootQuarterMass root z).toReal) h

def rootQuarterGhostDerivative (p : unitInterval) (h : ℝ) : ℝ :=
  Percolation.BenjaminiSchramm.ghostMagnetizationDerivative (Measure.count.prod (G.law p))
    (fun z => (G.rootQuarterMass root z).toReal) h

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_WeightedGhostIncidence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ghostBondWeight (o : V) (e : E) : ℝ≥0∞ :=
  ∑ v ∈ (G.ends e).toFinset, G.stabilizerWeight o v ^ (3 / 8 : ℝ)

def threeEighthMass (o : V) (S : Set V) : ℝ≥0∞ :=
  ∑' v, if v ∈ S then G.stabilizerWeight o v ^ (3 / 8 : ℝ) else 0

end CriticalPercolation.BondGraph

end

end OAI
end


